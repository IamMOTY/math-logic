module Main where
import Lexer
import Parser
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe

data Line = MP Int Int Int | Hypot Int Int | Axiom Int Int deriving (Eq, Ord)
data Tree = Node Int [Expr] Expr String

instance Show Tree where
    show (Node depth hypots expr def) = "[" ++ show depth ++ "] " ++ listToString hypots ++ "|-" ++ show expr ++ " " ++ def

instance Show Expr where
    show (a :->: b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (a :&: b) = "(" ++ show a ++ " & " ++ show b ++ ")"
    show (a :|: b) = "(" ++ show a ++ " | " ++ show b ++ ")"
    show (Neg expr) = "(" ++ show expr ++ " -> _|_ )"
    show (Var x) = x
    show Bottom = "_|_"

handle :: [String] -> [String]
handle (h : rest) = do
    let (hypotises, toProof) = parseHead $ alexScanTokens h
    let n = length hypotises
    let hypots = Map.fromList (zip (reverse hypotises) [1..n])
    let proof = map (parseProof . alexScanTokens) rest

    case verifyProof toProof Map.empty hypots Map.empty proof 1 Map.empty of
        (-1, proven, impls, ind2Expr) ->
            buildTree hypotises toProof ind2Expr proven 0 []
        (-2, _, _, _) -> ["The proof does not prove the required expression"]
        (ind, _, _, _) ->  ["Proof is incorrect at line "++show (ind + 1)]
handle [] = ["Empty input"]

listToString :: [Expr] -> String
listToString (h : rest) = show h ++ "," ++ listToString rest
listToString [] = ""

buildTree :: [Expr] -> Expr -> Map.Map Int Expr -> Map.Map Expr Line -> Int -> [String] -> [String]
buildTree hypots expr ind2Expr proven depth proof =
    case proven `get` expr of
      MP n i j -> buildTree hypots (ind2Expr `get` i) ind2Expr proven (depth + 1) [] ++ buildTree hypots (ind2Expr `get` j) ind2Expr proven (depth + 1) [] ++ show (Node depth hypots expr "[E->]") : proof
      Hypot n i -> show (Node depth hypots expr "[Ax]") : proof
      Axiom n i -> axiomToStringList depth hypots expr i

axiom :: Expr -> Int -> Map.Map Expr Line -> Maybe (Map.Map Expr Line)
axiom expr@(a :->: (b :->: a')) ind proven
 | a == a' = axiom' ind expr proven (Just 1)
axiom expr@((a :->: b) :->: ((a' :->: (b' :->: c)) :->: (a'' :->: c'))) ind proven
 | a == a' && a == a'' && b == b' && c == c' = axiom' ind expr proven (Just 2)
axiom  expr@(a :->: (b :->: (a' :&: b'))) ind proven
 | a == a' && b == b' = axiom' ind expr proven (Just 3)
axiom expr@((a :&: b) :->: a') ind proven
 | a == a' = axiom' ind expr proven (Just 4)
axiom expr@((a :&: b) :->: b') ind proven
 | b == b' = axiom' ind expr proven (Just 5)
axiom  expr@(a :->: (a' :|: b)) ind proven
 | a == a' = axiom' ind expr proven (Just 6)
axiom  expr@(b' :->: (a :|: b)) ind proven
 | b == b' = axiom' ind expr proven (Just 7)
axiom  expr@((a :->: c) :->: ((b :->: c') :->: ((a' :|: b') :->: c''))) ind proven
 | a == a' && b == b' && c == c' && c == c'' = axiom' ind expr proven (Just 8)
axiom  expr@((a :->: b) :->: ((a' :->: Neg b') :->: Neg a'')) ind proven
 | a == a' && a == a'' && b == b' = axiom' ind expr proven (Just 9)
axiom  expr@(a :->: (Neg a' :->: b)) ind proven
 | a == a' = axiom' ind expr proven (Just 10)
axiom _ _ _ = Nothing

axiom' :: Int -> Expr -> Map.Map Expr Line -> Maybe Int -> Maybe (Map.Map Expr Line)
axiom' _ _ _ Nothing = Nothing
axiom' ind expr proven (Just num) = Just (Map.insert expr (Axiom ind num) proven)

axiomToStringList :: Int -> [Expr] -> Expr -> Int -> [String]
axiomToStringList depth hypots expr 1 = do --
    let (a :->: (b :->: a')) = expr
    [show (Node (depth + 2) (a : b : hypots) a' "[Ax]"),
     show (Node (depth + 1) (a : hypots) (b :->: a') "[I->]"),
     show (Node depth hypots expr "[I->]")]
axiomToStringList depth hypots expr 2 = do --
    let ((a :->: b) :->: ((a' :->: (b' :->: c)) :->: (a'' :->: c'))) = expr
    [
     show (Node (depth + 5)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) (a :->: (b :->: c')) "[Ax]"),
     show (Node (depth + 5)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) a "[Ax]"),
     show (Node (depth + 4)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) (b :->: c') "[E->]"),
     show (Node (depth + 5)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) (a :->: b) "[Ax]"),
     show (Node (depth + 5)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) a "[Ax]"),
     show (Node (depth + 4)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) b "[E->]"),
     show (Node (depth + 3)  ((a :->: b) : (a' :->: (b' :->: c)) : a'' : hypots) c' "[E->]"),
     show (Node (depth + 2)  ((a :->: b) : (a' :->: (b' :->: c)) : hypots) (a'' :->: c') "[I->]"),
     show (Node (depth + 1) ((a :->: b): hypots) ((a' :->: (b' :->: c)) :->: (a'' :->: c')) "[I->]"),
     show (Node depth hypots expr "[I->]")]
axiomToStringList depth hypots expr 3 = do --
    let (a :->: (b :->: (a' :&: b'))) = expr
    [   
         show (Node (depth + 3) (a : b : hypots) a "[Ax]")
        , show (Node (depth + 3) (a : b : hypots) b "[Ax]")
        , show (Node (depth + 2) (a : b : hypots) (a' :&: b') "[I&]")
        , show (Node (depth + 1) (a : hypots) (b :->: (a' :&: b')) "[I->]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 4 = do --
    let ((a :&: b) :->: a') = expr
    [     show (Node (depth + 2) ((a :&: b) : hypots) (a :&: b) "[Ax]")
        , show (Node (depth + 1) ((a :&: b) : hypots) a "[El&]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 5 = do --
    let ((a :&: b) :->: b') = expr
    [     show (Node (depth + 2) ((a :&: b) : hypots) (a :&: b) "[Ax]")
        , show (Node (depth + 1) ((a :&: b) : hypots) b "[Er&]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 6 = do --
    let (a :->: (a' :|: b)) = expr
    [     show (Node (depth + 2) (a : hypots) a' "[Ax]")
        , show (Node (depth + 1) (a : hypots) (a' :|: b) "[Il|]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 7 = do --
    let (b :->: (a :|: b')) = expr
    [   
          show (Node (depth + 2) (b : hypots) b "[Ax]")
        , show (Node (depth + 1) (b : hypots) (a :|: b) "[Ir|]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 8 = do --
    let ((a :->: c) :->: ((b :->: c') :->: ((a' :|: b') :->: c''))) = expr
    [
         show (Node (depth + 5) ((a :->: c) : (b :->: c) : (a :|: b) : a: hypots) (a :->: c) "[Ax]")
        , show (Node (depth + 5) ((a :->: c) : (b :->: c) : (a :|: b) : a: hypots) a "[Ax]")
        , show (Node (depth + 4) ((a :->: c) : (b :->: c) : (a :|: b) : a: hypots) c "[E->]")
        , show (Node (depth + 5) ((a :->: c) : (b :->: c) : (a :|: b) : b: hypots) (b :->: c) "[Ax]")
        , show (Node (depth + 5) ((a :->: c) : (b :->: c) : (a :|: b) : b: hypots) b "[Ax]")
        , show (Node (depth + 4) ((a :->: c) : (b :->: c) : (a :|: b) : b: hypots) c "[E->]")
        , show (Node (depth + 4) ((a :->: c) : (b :->: c) : (a :|: b): hypots) (a :|: b) "[Ax]")
        , show (Node (depth + 3) ((a :->: c) : (b :->: c) : (a :|: b): hypots) c "[E|]")
        , show (Node (depth + 2) ((a :->: c) : (b :->: c): hypots) ((a :|: b) :->: c) "[I->]")
        , show (Node (depth + 1) ((a :->: c): hypots) ((b :->: c) :->: ((a :|: b) :->: c)) "[I->]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 9 = do --
    let ((a :->: b) :->: ((a' :->: Neg b') :->: Neg a'')) = expr
    [   
         show (Node (depth + 5) ((a :->: b) : (a' :->: Neg b') : a : hypots) (a :->: Neg b) "[Ax]")
        , show (Node (depth + 5) ((a :->: b) : (a' :->: Neg b') : a : hypots) a "[Ax]")
        , show (Node (depth + 4) ((a :->: b) : (a' :->: Neg b') : a : hypots) (Neg b) "[E->]")
        , show (Node (depth + 5) ((a :->: b) : (a' :->: Neg b') : a : hypots) (a :->: b) "[Ax]")
        , show (Node (depth + 5) ((a :->: b) : (a' :->: Neg b') : a : hypots) a "[Ax]")
        , show (Node (depth + 4) ((a :->: b) : (a' :->: Neg b') : a : hypots) b "[E->]")
        , show (Node (depth + 3) ((a :->: b) : (a' :->: Neg b') : a : hypots) Bottom "[E->]")
        , show (Node (depth + 2) ((a :->: b) : (a' :->: Neg b') : hypots) (Neg a'') "[I->]")
        , show (Node (depth + 1) ((a :->: b) : hypots) ((a' :->: Neg b') :->: Neg a'') "[I->]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList depth hypots expr 10 = do --
    let (a :->: (Neg a' :->: b)) = expr
    [ 
         show (Node (depth + 5) (a : Neg a' : Bottom : hypots)  Bottom "[Ax]")
        , show (Node (depth + 4) (a : Neg a' : Bottom : hypots)  b "[E_|_]")
        , show (Node (depth + 3) (a : Neg a' : hypots) (Bottom :->: b) "[I->]")
        , show (Node (depth + 4) (a : Neg a' : hypots) (Neg a) "[Ax]")
        , show (Node (depth + 4) (a : Neg a' : hypots) a "[Ax]")
        , show (Node (depth + 3) (a : Neg a' : hypots) Bottom "[E->]")
        , show (Node (depth + 2) (a : Neg a' : hypots) b "[E->]")
        , show (Node (depth + 1) (a : hypots) (Neg a' :->: b) "[I->]")
        , show (Node depth hypots expr "[I->]") ]
axiomToStringList _ _ _ _ =
    error "Axiom expanding error"

add :: Expr -> Map.Map Expr [(Expr, Int)] -> Int -> Map.Map Expr [(Expr, Int)]
add (v :->: k) impls ind =
     case Map.lookup k impls of
        Just vs -> Map.insert k ((v, ind) : vs) impls
        Nothing -> Map.insert k [(v, ind)] impls
add _ impls _ = impls

hypotCheck :: Map.Map Expr Int -> Expr -> Map.Map Expr Line -> Int -> Maybe (Map.Map Expr Line)
hypotCheck hypots expr proven ind = 
    case Map.lookup expr hypots of
        Just x -> Just (Map.insert expr (Hypot ind x) proven)
        Nothing -> Nothing

mp' :: [(Expr, Int)] -> Map.Map Expr Line -> Maybe (Int, Int)
mp' exprs proven = case filter (\(expr, indx) -> isJust (Map.lookup expr proven)) exprs of
    ((ex, ind) : _) -> 
        case Map.lookup ex proven of
            (Just (MP lineIndex a b)) -> Just (ind, lineIndex)
            (Just (Hypot lineIndex num)) -> Just (ind, lineIndex)
            (Just (Axiom lineIndex num)) -> Just (ind, lineIndex)
            Nothing -> error "Error occur while checking MP"
    []       -> Nothing

mp :: Map.Map Expr [(Expr, Int)] -> Expr -> Map.Map Expr Line -> Int -> Maybe (Map.Map Expr Line)
mp impls expr proven ind = case Map.lookup expr impls of
    Just lefts -> case mp' lefts proven of
        (Just (ind1, ind2)) -> Just (Map.insert expr (MP ind ind1 ind2) proven)
        Nothing -> Nothing
    Nothing -> Nothing

verifyLine :: Map.Map Expr Line -> Map.Map Expr Int -> Map.Map Expr [(Expr, Int)]  -> Expr -> Int -> Maybe  (Map.Map Expr Line)
verifyLine proven hypots impls expr ind = case Map.lookup expr proven of
    (Just _) -> Just proven 
    Nothing -> 
        case hypotCheck hypots expr proven ind of
            (Just proven') -> Just proven'
            Nothing        -> 
                case axiom expr ind proven of
                    (Just proven') -> Just proven'
                    Nothing -> mp impls expr proven ind

verifyProof :: Expr -> Map.Map Expr Line -> Map.Map Expr Int -> Map.Map Expr [(Expr, Int)] -> [Expr] -> Int -> Map.Map Int Expr -> (Int, Map.Map Expr Line, Map.Map Expr [(Expr, Int)], Map.Map Int Expr)
verifyProof toProof proven hypots impls [expr] ind  ind2Expr =
     if toProof == expr
     then 
         case verifyLine proven hypots impls expr ind of
                (Just proven') -> (-1,  proven', impls, Map.insert ind expr ind2Expr)
                Nothing        -> (ind, proven, impls, ind2Expr)
     else 
         (-2, proven, impls, ind2Expr)
verifyProof toProof proven hypots impls (expr : exprs) ind ind2Expr =
    case verifyLine proven hypots impls expr ind of
        (Just proven') -> verifyProof toProof proven' hypots (add expr impls ind) exprs (ind + 1) (Map.insert ind expr ind2Expr)
        Nothing        -> (ind, proven, impls, ind2Expr)
verifyProof _ _ _  _ [] _ _ = error "Error occur while verifing proof"

get :: (Ord a, Show a) => Map.Map a p -> a -> p
get m k = case Map.lookup k m of
    (Just v) -> v
    Nothing  -> error (show k)

main :: IO()
main = interact (unlines . handle . lines)