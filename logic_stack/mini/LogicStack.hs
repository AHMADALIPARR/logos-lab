-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
-- LogicStack.hs — FOIL + mini-Metagol + Tree
-- compile: ghc -O2 LogicStack.hs
module Main where
import Data.List (maximumBy, nub, foldl')
import Data.Ord (comparing)
import Data.Maybe (catMaybes)
import Data.Bits ((.&.), (.|.))
-- ============================================================
-- L0: BINARY SUBSTRATE
-- ============================================================
type Bit = Int
bits :: Int -> [[Bit]]
bits 0 = [[]]
bits n = [b:bs | b <- [0,1], bs <- bits (n-1)]
band, bor, bxor :: Bit -> Bit -> Bit
band = (.&.); bor = (.|.); bxor = xor' where xor' a b = a `bor` (b `band` 0) `bx'` b
bx' a b = (a `bor` b) `band` (1 - (a `band` b))
-- target concept: odd parity of bits
target :: [Bit] -> Bool
target = odd . sum
mkExamples :: Int -> ([Ex], [Ex])
mkExamples n = (filter target allB, filter (not . target) allB)
  where allB = bits n
-- ============================================================
-- L1: LOGIC — terms, unification, KB
-- ============================================================
data Term = C String          -- constant
          | V String          -- variable
          deriving (Eq, Show)
type Binding = [(Term, Term)]
type Atom = (String, [Term])
type Clause = (Atom, [Atom])  -- head :- body
subst :: Binding -> Term -> Term
subst b (V x) = case lookup (V x) b of
                  Just t  -> subst b t
                  Nothing -> V x
subst b (C x) = C x
unify :: [Term] -> [Term] -> Binding -> Maybe Binding
unify [] [] b = Just b
unify (x:xs) (y:ys) b =
  let x' = subst b x; y' = subst b y in
  case (x', y') of
    (a, c) | a == c -> unify xs ys b          -- identical after substitution (no self-binding)
    (V _, V _)   -> unify xs ys ((x', y'):b)
    (V _, _)     -> unify xs ys ((x', y'):b)
    (_, V _)     -> unify xs ys ((y', x'):b)
    (a, c) | a == c -> unify xs ys b
    _            -> Nothing
unify _ _ _ = Nothing
type KB = [Clause]
-- resolution: all bindings proving atom against KB (depth 1 + body)
prove :: KB -> Atom -> Binding -> [Binding]
prove kb a b = concat
  [ case unify (snd h) (snd a) b of
      Nothing -> []
      Just b1 -> foldl (\bs bodyLit -> concatMap (prove kb bodyLit) bs) [b1] body
  | (h, body) <- kb ]
-- ============================================================
-- L2: FOIL — literal-adding with info gain
-- ============================================================
type Ex = [Bit]
-- body literals are (predicate over example, required value)
data Lit = Has Int Bit          -- position i has bit v
         | ANDAt Int Int Bit    -- positions i,j ANDed = v
         | XorAt Int Int Bit    -- positions i,j XORed = v  (needed for parity)
         deriving (Eq, Show)
litHolds :: Lit -> Ex -> Bool
litHolds (Has i v) e     = (e !! i) == v
litHolds (ANDAt i j v) e = band (e !! i) (e !! j) == v
litHolds (XorAt i j v) e = bxor (e !! i) (e !! j) == v
type Rule = [Lit]
covers :: Rule -> Ex -> Bool
covers r e = all (`litHolds` e) r
entropy :: Double -> Double
entropy p | p <= 0 || p >= 1 = 0
          | otherwise = -(p * log p + (1-p) * log (1-p))
foilGain :: Rule -> [Ex] -> [Ex] -> Double
foilGain _ [] [] = 0
foilGain rule pos neg
  | tot == 0 = 0
  | otherwise =
      let sub = filter (covers rule) (pos ++ neg)
          sn  = length sub
      in if sn == 0 then 0
         else let sp  = length (filter (covers rule) pos)
                  p1  = fromIntegral sp / fromIntegral sn
                  pn  = length pos
                  p0  = fromIntegral pn / fromIntegral tot
              in entropy p0 - (fromIntegral sn / fromIntegral tot) * entropy p1
  where tot = length pos + length neg
-- greedy FOIL: add literal maximizing gain until pure
foil :: Int -> [Ex] -> [Ex] -> Rule
foil width pos neg = go []
  where
    go acc
      | null (filter (covers acc) neg) = acc
      | otherwise =
          let cands = [ l | l <- candidates width, notElem l acc ]
          in case cands of
               [] -> acc
               _  -> let best = maximumBy
                                (comparing (\l -> foilGain (l:acc) pos neg)) cands
                         -- plateau (e.g. parity: every single literal has gain 0): look ahead two literals
                         pairs = [ [l1,l2] | l1 <- cands, l2 <- cands, l1 /= l2 ]
                         bestP = maximumBy
                                (comparing (\ls -> (foilGain (ls ++ acc) pos neg, length (filter (covers (ls ++ acc)) pos)))) pairs  -- ties: more positives covered
                         prec ls = let c = length (filter (covers ls) pos)
                                       n = length (filter (covers ls) neg)
                                   in if c + n == 0 then 0 else fromIntegral c / fromIntegral (c + n) :: Double
                     in if prec (best:acc) > prec acc then go (best:acc)
                        else go (bestP ++ acc)
-- separate & conquer: learn clauses until every positive is covered
foilAll :: Int -> [Ex] -> [Ex] -> [Rule]
foilAll width pos neg = loop pos
  where loop [] = []
        loop ps = let r   = foil width ps neg
                      ps' = filter (not . covers r) ps
                  in if length ps' == length ps then [] else r : loop ps'
candidates :: Int -> [Lit]
candidates w = [Has i v | i <- [0..w-1], v <- [0,1]]
            ++ [ANDAt i j v | i <- [0..w-1], j <- [i+1..w-1], v <- [0,1]]
            ++ [XorAt i j v | i <- [0..w-1], j <- [i+1..w-1], v <- [0,1]]
-- ============================================================
-- L3: METAGOL — meta-interpretive learning with invention
-- meta-rule: chain  P(A,B) :- Q(A,C), R(C,B)
--            ident  P(A,B) :- Q(A,B)
-- invented predicate is a learned program fragment
-- ============================================================
type Metarule = String
metaRules :: [Metarule]
metaRules = ["chain", "ident"]
-- represent invented preds as index; programs are list of clauses
type Prog = [Clause]
-- mini MIL: learn pos/neg relation 'f(A,B)' over positions
-- target: next* (transitive closure) from BK 'next'
bk :: KB
bk = [ (("next", [C "0", C "1"]), [])
     , (("next", [C "1", C "2"]), [])
     , (("next", [C "2", C "3"]), []) ]
-- candidate programs: 0..2 invented chain applications
milCandidates :: [Prog]
milCandidates =
  [ [ fid "next" ] ]  -- ident: target directly = next
  ++ [ [ (("f", [V "A", V "B"]), [("next", [V "A", V "C"]), ("next", [V "C", V "B"])]) ]
     , [ inv1c, fid "next", fid "inv1" ]
     , [ inv1c, fid "next", fid "inv1"
       , (("f", [V "A", V "B"]), [("next", [V "A", V "C"]), ("inv1", [V "C", V "B"])]) ]
     ]  -- chain compositions, with invented inv1 = next;next
  where fid q = (("f", [V "A", V "B"]), [(q, [V "A", V "B"])])
        inv1c = (("inv1", [V "A", V "B"]),
                 [("next", [V "A", V "C"]), ("next", [V "C", V "B"])])
posPairs, negPairs :: [(String, String)]
posPairs = [("0","1"),("1","2"),("2","3"),("0","2"),("0","3"),("1","3")]
negPairs = [("3","0"),("2","0"),("3","1")]
progProves :: Prog -> (String, String) -> Bool
progProves p (a,b) =
  not (null (prove' (bk ++ p) ("f", [C a, C b]) []))
  where
    -- like prove, but renames the clause variables apart on every call
    prove' kb' q@(_, args) bnd = concat
      [ case unify (snd h') args bnd of
          Nothing -> []
          Just b1 -> foldl (\bs l -> concatMap (prove' kb' l) bs) [b1] body'
      | (h, body) <- kb', fst h == fst q, length (snd h) == length args
      , let tag = "'" ++ show (length bnd)
            rn (V x) = V (x ++ tag)
            rn t     = t
            h'    = (fst h, map rn (snd h))
            body' = [ (n, map rn ts) | (n, ts) <- body ] ]
-- simplified: direct proof search for f over the candidate programs
solve :: (String,String) -> Bool
solve (a,b) = any (\pr -> progProves pr (a,b)) milCandidates
-- METAGOL step: pick program consistent with pos/neg
metagol :: Maybe Prog
metagol =
  let progs = [ p | p <- milCandidates
              , all (\(a,b) -> progProves p (a,b)) posPairs
              , not (any (\(a,b) -> progProves p (a,b)) negPairs) ]
  in case progs of (p:_) -> Just p; [] -> Nothing
-- ============================================================
-- L4: TREE — rules as a decision tree
-- ============================================================
data Tree = Node String [Tree]
          | Leaf String Bool
          deriving Show
ruleToTree :: Rule -> Tree
ruleToTree [] = Leaf "default" True
ruleToTree (l:rest) = Node (show l) [ruleToTree rest]
main :: IO ()
main = do
  let width = 4
      (pos, neg) = mkExamples width
      rules = foilAll width pos neg
      ok e = any (`covers` e) rules == target e
  putStrLn $ "=== L0: " ++ show (length pos) ++ " pos / "
           ++ show (length neg) ++ " neg examples ==="
  putStrLn "=== L2: FOIL rule ==="
  mapM_ print rules
  putStrLn "=== L3: Metagol invented program ==="
  case metagol of
    Just p  -> print p
    Nothing -> putStrLn "(consistent BK only)"
  putStrLn "=== L4: Tree ==="
  mapM_ (putStrLn . draw . ruleToTree) rules   -- one branch per learned clause (disjunction)
  putStrLn $ "=== training accuracy: " ++ show (fromIntegral (length (filter ok (pos ++ neg))) / fromIntegral (length (pos ++ neg)) :: Double) ++ " ==="
  where
    draw (Leaf s v) = "  -> " ++ s ++ " = " ++ show v
    draw (Node s k) = s ++ "\n" ++ unlines (map (("  |" ++) . draw) k)
