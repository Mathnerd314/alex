{
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where
import System.Exit
import Data.ByteString.Lazy.Char8 (unpack)
}

%wrapper "posn-bytestring"
%encoding "UTF8"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

  $white+				;
  "--".*				;
  let					{ tok (\p s -> Let p) }
  in					{ tok (\p s -> In p) }
  $digit+                               { tok (\p s -> Int p (read (unpack s))) }
  [\=\+\-\*\/\(\)]                      { tok (\p s -> Sym p (head (unpack s))) }
  $alpha [$alpha $digit \_ \']*         { tok (\p s -> Var p (unpack s)) }

{
-- Each right-hand side has type :: AlexPosn -> String -> Token

-- Some action helpers:
tok f p s = f p s

-- The token type:
data Token =
	Let AlexPosn		|
	In  AlexPosn		|
	Sym AlexPosn Char	|
        Var AlexPosn String     |
	Int AlexPosn Int	|
	Err AlexPosn
	deriving (Eq,Show)

main = if test1 /= result1 then exitFailure
			   else exitWith ExitSuccess

test1 = alexScanTokens "  let in 012334\n=+*foo bar__'"
result1 = [Let (AlexPn 2 1 3),In (AlexPn 6 1 7),Int (AlexPn 9 1 10) 12334,Sym (AlexPn 16 2 1) '=',Sym (AlexPn 17 2 2) '+',Sym (AlexPn 18 2 3) '*',Var (AlexPn 19 2 4) "foo",Var (AlexPn 23 2 8) "bar__'"]


}
