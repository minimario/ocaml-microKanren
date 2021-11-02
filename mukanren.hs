import Control.Monad
import Control.Applicative

type Var = Integer
type Subst = [(Var, Term)]
type State = (Subst, Integer)
type Program = State -> KList State

data Term = Atom String | Pair Term Term | Var Var deriving Show

-- Apply a substitution to the top level of a term

walk :: Term -> Subst -> Term
walk (Var v) s = case lookup v s of Nothing -> Var v
                                    Just us -> walk us s
walk u s = u

extS :: Var -> Term -> Subst -> Subst
extS x v s = (x, v) : s

-- Try to unify two terms under a substitution;
-- return an extended subst if it succeeds
unify :: Term -> Term -> Subst -> Maybe Subst
unify u v s = un (walk u s) (walk v s)
  where un (Var x1) (Var x2) | x1 == x2 = return s
        un (Var x1) v = return $ extS x1 v s
        un u (Var x2) = return $ extS x2 u s
        un (Pair u1 u2) (Pair v1 v2) =
          do s' <- unify u1 v1 s
             unify u2 v2 s'
        un (Atom a1) (Atom a2) | a1 == a2 = return s
        un _ _  = mzero

-- MicroKanren program formers
zzz :: Program -> Program
zzz g = \sc -> delay (g sc)

equiv :: Term -> Term -> Program
equiv u v = \(s, c) -> case unify u v s of
  Nothing -> mzero
  Just s' -> return (s', c)

callFresh :: (Term -> Program) -> Program
callFresh f = \(s, c) -> f (Var c) (s, c+1)

disj :: Program -> Program -> Program
disj g1 g2 = \sc -> mplus (g1 sc) (g2 sc)

conj :: Program -> Program -> Program
conj g1 g2 = \sc -> g1 sc >>= g2

-- I had originally thought that since Haskell was lazy, we didn't
-- need to worry about any of the inverse-eta-delay stuff that the
-- Scheme version does, but that isn't right. We still need some way
-- to force switching when we recur.
-- It is not very burdensome for us, though; we don't actually need
-- to eta-expand, just need to add some sort of marker.
data KList a = Nil | Cons a (KList a) | Delay (KList a) deriving Show
delay = Delay

-- Hm. Is there any reason to preserve the delays?
instance Monad KList where
  return x = Cons x Nil
  Nil >>= f = mzero
  x `Cons` xs >>= f = f x `mplus` (xs >>= f)
  Delay xs >>= f = Delay (xs >>= f)

instance Alternative KList where
  (<|>) = mplus
  empty = mzero

instance MonadPlus KList where
  mzero = Nil
  Nil `mplus` xs = xs
  (x `Cons` xs) `mplus` ys = x `Cons` (ys `mplus` xs) -- swapped per sect. 6
  Delay xs `mplus` ys = Delay (ys `mplus` xs)

klistToList Nil = []
klistToList (x `Cons` xs) = x : klistToList xs
klistToList (Delay xs) = klistToList xs

-------------- Test cases
empty_state = ([], 0)

five = callFresh (\x -> equiv x (Atom "5"))
fives_ x = disj (equiv x (Atom "5")) (zzz $ fives_ x)
fives = callFresh fives_

fivesRev_ x = disj (zzz $ fivesRev_ x) (equiv x (Atom "5"))
fivesRev = callFresh fivesRev_

a_and_b = conj
          (callFresh (\a -> equiv a (Atom "7")))
          (callFresh (\b -> disj (equiv b (Atom "5")) (equiv b (Atom "6"))))

runTest p = klistToList (p empty_state)