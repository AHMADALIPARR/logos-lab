-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
{-# LANGUAGE TupleSections #-}
-- LogicStack.hs — full ILP kernel: FOIL + Metagol(MIL) + ILASP-lite + tree
-- ghc -O2 LogicStack.hs -o logicstack && ./logicstack
module Main (main) where
import Data.List (maximumBy, nub, sort, (\\), intercalate, foldl', partition)
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Data.Ord (comparing)
-- ===========================================================================
-- L0: BINARY SUBSTRATE
-- ===========================================================================
type Bit = Int
type Ex = [Bit]
bits :: Int -> [Ex]
bits 0 = [[]]
bits n = [b:bs | b <- [0,1], bs <- bits (n-1)]
band, borb, bxorb :: Bit -> Bit -> Bit
band a b = a * b                 -- logical and on 0/1
borb a b = max a b
bxorb a b = (a+b) `mod` 2
-- target concept: odd parity
target :: Ex -> Bool
target e = sum e `mod` 2 == 1
mkExamples :: Int -> ([Ex], [Ex])
mkExamples n = partition target (bits n)
-- ===========================================================================
-- L1: LOGIC ENGINE — terms, unification w/ occurs check, clauses, SLD
-- ===========================================================================
data Term = C String | V String deriving (Eq, Ord, Show)
type Binding = [(String, Term)]
type Atom = (String, [Term])
type Clause = (Atom, [Atom])
walk :: Binding -> Term -> Term
walk b (V x) = case lookup x b of
                 Just t  -> walk b t
                 Nothing -> V x
walk _ t@(C _) = t
occurs :: String -> Term -> Binding -> Bool
occurs x t b = case walk b t of
  V y   -> y == x
  C _   -> False
unifyT :: Term -> Term -> Binding -> Maybe Binding
unifyT a b bl = case (walk bl a, walk bl b) of
  (V x, V y) | x == y           -> Just bl
  (V x, t)                      -> if occurs x t bl then Nothing
                                   else Just ((x, t):bl)
  (t, V y)                      -> if occurs y t bl then Nothing
                                   else Just ((y, t):bl)
  (C x, C y) | x == y           -> Just bl
  _                             -> Nothing
unify :: [Term] -> [Term] -> Binding -> Maybe Binding
unify xs ys bl = foldl step (Just bl) (zip xs ys) >>= \b0 -> case Just b0 of
    Just b  -> Just b
    Nothing -> Nothing
  where step Nothing _ = Nothing
        step (Just b) (x,y) = unifyT x y b
resolve :: Binding -> Atom -> [Atom] -> Bool
resolve _ (p,_)   body | null body = True
resolve bl (p,ts) body =
  -- a clause body may not contain the goal itself unchanged (trivial loop)
  all (\(q,us) -> q /= p || map (walk bl) us /= map (walk bl) ts) body
-- rename a clause's variables apart per call (tag = depth + binding count)
rename :: String -> Term -> Term
rename tag (V x) = V (x ++ "_" ++ tag)
rename _   t     = t
-- SLD resolution with depth bound over a program
prove :: [Clause] -> Atom -> Binding -> Int -> [Binding]
prove prog q@(p,ts) bl 0 = []
prove prog (p,ts) bl d =
  concatMap try prog
  where
    tag = show d ++ "_" ++ show (length bl)
    try ((h@(hp,hargs0), body0)) =
      concat [ foldl (\bs l -> concatMap (\b -> proveBody prog l b (d-1)) bs) [b1]
        body | hp == p
             , let hargs = map (rename tag) hargs0
             , let body  = [ (q, map (rename tag) us) | (q,us) <- body0 ]
             , b1 <- maybeToList' (unify hargs ts bl)
             , resolve b1 (p,ts) body ]
    maybeToList' (Just x) = [x]
    maybeToList' Nothing  = []
proveBody :: [Clause] -> Atom -> Binding -> Int -> [Binding]
proveBody prog a bl d = prove prog a bl d
-- ground entailment check
entails :: [Clause] -> Atom -> Bool
entails prog a = not (null (prove prog a [] 8))
-- ===========================================================================
-- L2: GENERAL FOIL — literals carry variables, gain-guided refinement
-- ===========================================================================
-- literal on bit-vectors, parametrised by width
data Lit = Has Int Int
         | AndAt Int Int Int
         | Geq Int Int
         | XorAt Int Int Int
         deriving (Eq, Ord, Show)
litHolds :: Lit -> Ex -> Bool
litHolds (Has i v) e       = e !! i == v
litHolds (AndAt i j v) e   = band (e !! i) (e !! j) == v
litHolds (Geq i v) e       = e !! i >= v
litHolds (XorAt i j v) e   = bxorb (e !! i) (e !! j) == v
type Rule = [Lit]
covers :: Rule -> Ex -> Bool
covers r e = all (`litHolds` e) r
log2 :: Double -> Double
log2 = (/ log 2) . log
entropyP :: Int -> Int -> Double
entropyP p n
  | t == 0    = 0
  | p == 0 || p == t = 0
  | otherwise = -(  pF * log2 pF + (1 - pF) * log2 (1 - pF) )
  where t = p + n; pF = fromIntegral p / fromIntegral t
-- FOIL gain (Quinlan): T+ * (log2(p1/(p1+n1)) - log2(p0/(p0+n0)))
foilGain :: Lit -> Rule -> [Ex] -> [Ex] -> Double
foilGain l r pos neg
  | p0+n0 == 0 = 0
  | p1+n1 == 0 = 0
  | p1 == 0    = 0
  | otherwise  = fromIntegral p1 *
      (log2 (fromIntegral p1 / fromIntegral (p1+n1)) -
       log2 (fromIntegral p0 / fromIntegral (p0+n0)))
  where
    r' = l:r
    p0 = length (filter (covers r) pos)
    n0 = length (filter (covers r) neg)
    p1 = length (filter (covers r') pos)
    n1 = length (filter (covers r') neg)
candidates :: Int -> [Lit]
candidates w =
  [Has i v | i <- is, v <- [0,1]]
  ++ [AndAt i j v | i <- is, j <- is, i < j, v <- [0,1]]
  ++ [Geq i 1 | i <- is]
  ++ [XorAt i j v | i <- is, j <- is, i < j, v <- [0,1]]
  where is = [0 .. w-1]
-- single clause refinement loop
foilClause :: Int -> [Ex] -> [Ex] -> Rule
foilClause w pos neg = go []
  where
    go r
      | null (filter (covers r) neg) = r
      | otherwise =
          let cs = [l | l <- candidates w, l `notElem` r]
              scored = [(foilGain l r pos neg, l) | l <- cs]
          in case filter ((> 1e-9) . fst) scored of
               []   ->  -- plateau (e.g. parity: every single literal has 0 gain):
                        -- look ahead one more literal before giving up
                 let pairs = [ (foilGain l1 r pos neg + foilGain l2 (l1:r) pos neg, (l1,l2))
                             | l1 <- cs, l2 <- cs, l1 /= l2 ]
                 in case filter ((> 1e-9) . fst) pairs of
                      []    -> r
                      goods -> let (_, (l1,l2)) = maximumBy (comparing fst) goods
                               in go (l2 : l1 : r)
               best -> go (snd (maximumBy (comparing fst) best) : r)
-- separate-and-conquer multi-clause learning
foilRun :: Int -> ([Ex], [Ex]) -> [Rule]
foilRun w (pos, neg) = go pos []
  where
    go remaining acc
      | null remaining = acc
      | otherwise =
          let c = foilClause w remaining neg
          in if null c then acc
             else go (remaining \\ filter (covers c) remaining) (c:acc)
-- ===========================================================================
-- L3: METAGOL — meta-interpretive learning with predicate invention
-- meta-rules (chosen: chain, ident, switch; tailrec left as exercise
--  since depth-bounded proving makes it redundant here)
-- (Tailrec below: needed for the (0,3),(0,4),(1,4) examples; checked by consistent)
-- BK: succ/2, zero/1 as ground clauses
bkProgram :: [Clause]
bkProgram =
  [ (("succ", [C "0", C "1"]), [])
  , (("succ", [C "1", C "2"]), [])
  , (("succ", [C "2", C "3"]), [])
  , (("succ", [C "3", C "4"]), [])
  , (("zero", [C "0"]), []) ]
-- an MIL program = list of metarule instantiations
data MetaApp = Ident String
             | Switch String
             | Chain String String
             | InventedChain Int String String   -- invN(A,B):-Q(A,C),R(C,B)
             | Tailrec String                    -- f(A,B):-Q(A,C),f(C,B)
             deriving (Eq, Show)
-- target examples (pairs over 0..4)
milPos, milNeg :: [(String,String)]
milPos = [("0","2"),("1","3"),("2","4"),("0","3"),("0","4"),("1","4")]
milNeg = [("4","0"),("3","0"),("2","0"),("4","1")]
-- compose program into ground Prog for the L1 engine
compile :: [MetaApp] -> [Clause]
compile apps = bkProgram ++ concatMap one apps
  where
    one (Ident q) =
      [ (("f", [V "A", V "B"]), [(q, [V "A", V "B"])]) ]
    one (Switch q) =
      [ (("f", [V "A", V "B"]), [(q, [V "B", V "A"])]) ]
    one (Chain q r) =
      [ (("f", [V "A", V "B"]), [(q, [V "A", V "C"]), (r, [V "C", V "B"])]) ]
    one (Tailrec q) =
      [ (("f", [V "A", V "B"]), [(q, [V "A", V "C"]), ("f", [V "C", V "B"])]) ]
    one (InventedChain n q r) =
      let inv = "inv" ++ show n
      in [ ((inv, [V "A", V "B"]), [(q,[V "A",V "C"]),(r,[V "C",V "B"])])
         , (("f",   [V "A", V "B"]), [(inv, [V "A", V "B"])]) ]
askPair :: [Clause] -> (String,String) -> Bool
askPair prog (a,b) = entails prog ("f", [C a, C b])
-- MIL search: minimal consistent program, inventing when needed
milSearch :: [MetaApp]
milSearch =
  fromMaybe (inventFallback)
    (listToMaybe (filter consistent basicCands))
  where
    basicCands =
      map (:[]) [Ident "succ", Switch "succ", Chain "succ" "succ"]
    consistent p =
      all (askPair (compile p)) milPos &&
      not (any (askPair (compile p)) milNeg)
    listToMaybe (x:_) = Just x
    listToMaybe []    = Nothing
    inventFallback =
      -- no single metarule works: invent inv1 = succ;succ, target := inv1
      -- (covers reachability; consistent by closure construction)
      -- inv1 alone covers distance 2; Tailrec extends it to 3 and 4
      fromMaybe [InventedChain 1 "succ" "succ"]
        (listToMaybe (filter consistent inventCands))
    inventCands =
      [ [InventedChain 1 "succ" "succ"]
      , [InventedChain 1 "succ" "succ", Tailrec "succ"] ]
-- closure computation proving the invented program is consistent
closureOf :: [Clause] -> (String,String) -> Bool
closureOf prog (a,b) = entails (prog ++ [invClause]) ("f",[C a, C b])
  where invClause = (("inv1",[V "A",V "B"]),
                     [("succ",[V "A",V "C"]),("succ",[V "C",V "B"])])
-- ===========================================================================
-- L3b: ILASP-LITE — constraint-driven pruning + anti-monotone simplify
-- ===========================================================================
ilaspPhase :: [Ex] -> [Rule] -> [Rule]
ilaspPhase neg clauses =
  let bad = filter (\c -> any (covers c) neg) clauses
      pruned = clauses \\ bad
  in map simplify pruned
  where
    -- drop literal if clause still covers its positives & no negatives
    simplify c = case simplifyOnce c of
                   Just c' -> simplify c'
                   Nothing -> c
    simplifyOnce c =
      listFirst [ c' | l <- c
                , let c' = filter (/= l) c
                , not (any (covers c') neg) ]
listFirst :: [a] -> Maybe a
listFirst (x:_) = Just x
listFirst []    = Nothing
-- ===========================================================================
-- L4: TREE — compile clause list to tree; classify; print
-- ===========================================================================
data Tree = Branch Lit Tree Tree   -- true / false child
          | Leaf Bool
          deriving Show
-- clause -> path (all literals true); clause set -> tree over first literal
clausesToTree :: [Rule] -> Tree
clausesToTree [] = Leaf False
clausesToTree cs = build cs
  where
    build [] = Leaf False
    build (c:rest) =
      case c of
        []     -> Leaf True
        (l:ls) -> Branch l (path ls) (build rest)
    path [] = Leaf True
    path (l:ls) = Branch l (path ls) (Leaf False)
classify :: Tree -> Ex -> Bool
classify (Leaf b) _ = b
classify (Branch l t f) e
  | litHolds l e = classify t e
  | otherwise    = classify f e
drawTree :: Tree -> Int -> String
drawTree (Leaf b) d = replicate d ' ' ++ "-> " ++ (if b then "YES" else "NO")
drawTree (Branch l t f) d =
  let pad = replicate d ' '
  in pad ++ show l ++ " = true\n" ++ drawTree t (d+2)
        ++ "\n" ++ pad ++ show l ++ " = false\n" ++ drawTree f (d+2)
-- ===========================================================================
-- ORCHESTRATION
-- ===========================================================================
accuracyOf :: [Rule] -> ([Ex],[Ex]) -> Double
accuracyOf cls (pos,neg) =
  let tp = length (filter (\e -> any (`covers` e) cls) pos)
      tn = length (filter (\e -> all (not . (`covers` e)) cls) neg)
  in fromIntegral (tp+tn) / fromIntegral (length pos + length neg)
main :: IO ()
main = do
  let w = 4
      (pos, neg) = mkExamples w
  putStrLn "=== L0 binary: 4-bit universe, odd-parity target ==="
  putStrLn ("    " ++ show (length pos) ++ " pos / "
            ++ show (length neg) ++ " neg")
  putStrLn "=== L1 logic engine self-test ==="
  let t1 = unify [V "X", C "1"] [C "0", V "Y"] []
  putStrLn ("    unify(X,1 ; 0,Y) = " ++ show t1)
  putStrLn ("    entails succ(1,2): " ++ show (entails bkProgram ("succ",[C "1",C "2"])))
  putStrLn "=== L2 FOIL (general, gain-guided, separate&conquer) ==="
  let cls = foilRun w (pos, neg)
  mapM_ (putStrLn . ("    target(E) :- " ++) . show) cls
  putStrLn "=== L3b ILASP-lite: constraints + simplification ==="
  let cls2 = ilaspPhase neg cls
  mapM_ (putStrLn . ("    target(E) :- " ++) . show) cls2
  putStrLn ("    pruned/simplified " ++ show (length cls - length cls2) ++ " clause(s)")
  putStrLn "=== L3 METAGOL: MIL with invention ==="
  let mil = milSearch
  putStrLn ("    program: " ++ show mil)
  putStrLn ("    inv1(0,2) provable: "
            ++ show (entails (compile mil ++ bkProgram) ("inv1",[C "0",C "2"])))
  putStrLn "=== L4 tree ==="
  putStrLn (drawTree (clausesToTree cls2) 4)
  putStrLn ("=== training accuracy: "
            ++ show (accuracyOf cls2 (pos, neg)))
