-- -----------------------------------------------------------------------------
--
-- Main.hs, part of Alex
--
-- (c) Chris Dornan 1995-2000, Simon Marlow 2003
--
-- ----------------------------------------------------------------------------}

module AlexTH (alexQ) where

import AbsSyn
import CharSet
import DFA
import DFAMin
import NFA
import Info
import Map ( Map )
import qualified Map hiding ( Map )
import Output
import ParseMonad ( runP )
import Parser
import Scan
import Util
import Paths_alex ( version, getDataDir )

import Control.Exception ( bracketOnError )
import Control.Monad ( when, liftM )
import Data.Maybe ( isJust, fromJust )
import Data.Version ( showVersion )
import System.Console.GetOpt ( getOpt, usageInfo, ArgOrder(..), OptDescr(..), ArgDescr(..) )
import System.Directory ( removeFile )
import System.Environment ( getProgName, getArgs )
import System.Exit ( ExitCode(..), exitWith )
import System.IO ( stderr, Handle, IOMode(..), openFile, hClose, hPutStr, hPutStrLn )
import System.IO ( hGetContents, hSetEncoding, utf8 )

import Data.Array
import Data.Array.Base (unsafeRead, unsafeAt)
import GHC.Exts
import System.IO
import System.IO.Unsafe
import Debug.Trace

import qualified Map
import qualified Data.IntMap as IntMap

import Control.Monad.ST ( ST, runST )
import Data.Array.ST ( STUArray, newArray, readArray, writeArray, freeze )
import Data.Array.Unboxed ( UArray, elems, (!), array, listArray )
import Data.Bits
import Data.Char ( ord, chr )
import Data.List ( isSuffixOf, nub, maximumBy, sortBy, groupBy, mapAccumR )

initialParserEnv :: (Map String CharSet, Map String RExp)
initialParserEnv = (initSetEnv, initREEnv)

initSetEnv :: Map String CharSet
initSetEnv = Map.fromList [("white", charSet " \t\n\v\f\r"),
                           ("printable", charSetRange (chr 32) (chr 0x10FFFF)), -- FIXME: Look it up the unicode standard
                           (".", charSetComplement emptyCharSet
                            `charSetMinus` charSetSingleton '\n')]

initREEnv :: Map String RExp
initREEnv = Map.empty

quoteDec  :: String -> Q [Dec]
quoteDec = quoteDecArgs 8

quoteDecArgs :: Int -> String -> Q [Dec]
quoteDecArgs tab_size file = do
  file <- location
  script <- parseScript file prg
  alex tab_size file script

parseScript :: Location -> String -> Q (Maybe (AlexPosn,Code), [Directive], Scanner, Maybe (AlexPosn,Code))
parseScript (Loc file _ _ (l,c) _) prg =
  case runP prg initialParserEnv parse of
        Left (Just (AlexPn _ line col),err) -> do
                let line' = l + line - 1
                    col' = if line' == l then c + col else col
                fail (file ++ ":" ++ show line' ++ ":" ++ show col'
                                 ++ ": " ++ err ++ "\n")
        Left (Nothing, err) ->
                fail (file ++ ": " ++ err ++ "\n")

        Right script -> return script

alex :: Int -> Location -> Scheme
     -> ([Directive], Scanner)
     -> Q [Dec]
alex tab_size file scheme (directives, scanner1) = do
   scheme <- getScheme directives
   let
         (scanner2, scs, sc_hdr) = encodeStartCodes scanner1
         (scanner_final, actions) = extractActions scheme scanner2
         encodingsScript = [ e | EncodingDirective e <- directives ]

   encoding <- case nub encodingsScript of
     []  -> return UTF8 -- default
     [e] -> return e
     _ -> fail "conflicting %encoding directives"

   let dfa = scanner2dfa encoding scanner_final scs
       min_dfa = minimizeDFA dfa
       nm  = scannerName scanner_final
       usespreds = usesPreds min_dfa

   put_info "\nStart codes\n"
   put_info (show $ scs)
   put_info "\nScanner\n"
   put_info (show $ scanner_final)
   put_info "\nNFA\n"
   put_info (show $ scanner2nfa encoding scanner_final scs)
   put_info "\nDFA"
   put_info (infoDFA 1 nm dfa "")
   put_info "\nMinimized DFA"
   put_info (infoDFA 1 nm min_dfa "")

   -- Inject the tab size
   hPutStrLn out_h $ "alex_tab_size :: Int"
   hPutStrLn out_h $ "alex_tab_size = " ++ show (tab_size :: Int)
   hPutStr out_h (outputDFA scheme min_dfa "")
   hPutStr out_h (sc_hdr "")
   hPutStr out_h (actions "")

-- -----------------------------------------------------------------------------
-- Printing the output

outputDFA :: Scheme -> DFA SNum Code -> Q [Dec]
outputDFA scheme dfa
  = sequence [outputBase, outputTable, outputCheck, outputDefault,outputAccept, outputActions, outputSigs]
  where
    (base, table, check, deflt, accept) = mkTables dfa

    intty = "Int"

    table_size = length table - 1
    n_states   = length base - 1

    base_nm   = "alex_base"
    table_nm  = "alex_table"
    check_nm  = "alex_check"
    deflt_nm  = "alex_deflt"
    accept_nm = "alex_accept"
    actions_nm = "alex_actions"

    outputBase    = do_array hexChars32 base_nm  n_states   base
    outputTable   = do_array hexChars16 table_nm table_size table
    outputCheck   = do_array hexChars16 check_nm table_size check
    outputDefault = do_array hexChars16 deflt_nm n_states   deflt

    do_array hex_chars nm upper_bound ints =
      [q| $nm :: Array Int Int
          $nm = listArray (0,$(shows upper_bound)) [$(interleave_shows (char ',') (map shows ints))]
      |]

    outputAccept =
      let
        userStateTy = case scheme of
          Monad { monadUserState = True } -> "AlexUserState"
          _ -> "()"
      in
        [q| $accept_nm :: Array Int (AlexAcc $userStateTy)
            $accept_nm = listArray (0::Int,$(shows n_states)) [$(interleave_shows (char ',') (snd (mapAccumR outputAccs 0 accept)))]
          |]

    gscanActionType res = [t| AlexPosn -> Char -> String -> Int -> ((Int, state) -> $res) -> (Int, state) -> $res |]

    outputActions
        = let
            (nacts, acts) = mapAccumR outputActs 0 accept
          in
            [q| $actions_nm :: Array Int $actionty
                $actions_nm = array (0,$(shows nacts)) [$(interleave_shows (char ',') (concat acts))]
            |]
    outputSigs
        = [q| 
              alex_scan_tkn :: () -> AlexInput -> $intty -> AlexLastAcc -> (AlexLastAcc, AlexInput)
              alexScanUser :: () -> AlexInput -> Int -> AlexReturn ($toktype)
              alexScan :: AlexInput -> Int -> AlexReturn ($toktype)
            |]

    outputAccs :: Int -> [Accept Code] -> (Int, ShowS)
    outputAccs idx [] = (idx, str "AlexAccNone")
    outputAccs idx (Acc _ Nothing Nothing NoRightContext : [])
      = (idx, str "AlexAccSkip")
    outputAccs idx (Acc _ (Just _) Nothing NoRightContext : [])
      = (idx + 1, str "AlexAcc " . str (show idx))
    outputAccs idx (Acc _ Nothing lctx rctx : rest)
      = let (idx', rest') = outputAccs idx rest
        in (idx', str "AlexAccSkipPred" . space
                 . paren (outputPred lctx rctx)
                 . paren rest')
    outputAccs idx (Acc _ (Just _) lctx rctx : rest)
      = let (idx', rest') = outputAccs idx rest
        in (idx' + 1, str "AlexAccPred" . space
                      . str (show idx') . space
                      . paren (outputPred lctx rctx)
                      . paren rest')

    outputActs :: Int -> [Accept Code] -> (Int, [ShowS])
    outputActs idx =
      let
        outputAct _ (Acc _ Nothing _ _) = error "Shouldn't see this"
        outputAct inneridx (Acc _ (Just act) _ _) =
          (inneridx + 1, paren (shows inneridx . str "," . str act))
      in
        mapAccumR outputAct idx . filter (\(Acc _ act _ _) -> isJust act)

    outputPred (Just set) NoRightContext
        = outputLCtx set
    outputPred Nothing rctx
        = outputRCtx rctx
    outputPred (Just set) rctx
        = outputLCtx set
        . str " `alexAndPred` "
        . outputRCtx rctx

    outputLCtx set = str "alexPrevCharMatches" . str (charSetQuote set)

    outputRCtx NoRightContext = id
    outputRCtx (RightContextRExp sn)
        = str "alexRightContext " . shows sn
    outputRCtx (RightContextCode code)
        = str code

    -- outputArr arr
        -- = str "array " . shows (bounds arr) . space
        -- . shows (assocs arr)

-----------------------------------------------------------------------------
-- Convert an integer to a 16-bit number encoded in \xNN\xNN format suitable
-- for placing in a string (copied from Happy's ProduceCode.lhs)

hexChars16 :: [Int] -> String
hexChars16 acts = concat (map conv16 acts)
  where
    conv16 i | i > 0x7fff || i < -0x8000
                = error ("Internal error: hexChars16: out of range: " ++ show i)
             | otherwise
                = hexChar16 i

hexChars32 :: [Int] -> String
hexChars32 acts = concat (map conv32 acts)
  where
    conv32 i = hexChar16 (i .&. 0xffff) ++
                hexChar16 ((i `shiftR` 16) .&. 0xffff)

hexChar16 :: Int -> String
hexChar16 i = toHex (i .&. 0xff)
                 ++ toHex ((i `shiftR` 8) .&. 0xff)  -- force little-endian

toHex :: Int -> String
toHex i = ['\\','x', hexDig (i `div` 16), hexDig (i `mod` 16)]

hexDig :: Int -> Char
hexDig i | i <= 9    = chr (i + ord '0')
         | otherwise = chr (i - 10 + ord 'a')
