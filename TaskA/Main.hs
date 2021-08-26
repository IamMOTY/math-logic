{-# LANGUAGE BlockArguments #-}
module Main where
import Lexer
import Parser
instance Show Expr where
    show (a :->: b) = "(->," ++ show a ++ "," ++ show b ++ ")"
    show (a :&: b) = "(&," ++ show a ++ "," ++ show b ++ ")"
    show (a :|: b) = "(|," ++ show a ++ "," ++ show b ++ ")"
    show (Neg expr) = "(!" ++ show expr ++ ")"
    show (Var x) = x

main :: IO ()
main = interact (show . parseExpr . alexScanTokens)
