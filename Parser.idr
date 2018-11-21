module Parser

import Data.Vect

import TypeOperators
import Box
import Success

%default total

record Parser (a : Type) (n : Nat) where
  constructor MkParser
  RunParser : {m : Nat} -> LTE m n -> Vect m Char -> List (Success a m)

map : (a -> b) -> Parser a i -> Parser b i
map f pa = MkParser (\prf, xs => map (map f) (RunParser pa prf xs)) --where
  -- runpb : LTE m i -> Vect m Char -> List (Success b m)
  -- runpb prf xs = 

anyChar : All (Parser Char)
anyChar {j} = MkParser anychar where
  anychar : LTE len j -> Vect len Char -> List (Success Char len)
  anychar prf [] = []
  anychar prf (x :: xs) = [MkSuccess x (LTESucc lteRefl) xs]

guardM : (a -> Maybe b) -> Parser a i -> Parser b i
guardM f {a} {b} pa {i} = MkParser runpb where
  runpb : LTE m i -> Vect m Char -> List (Success b m)
  runpb prf xs = 
    let 
      res1 = RunParser (map f pa) prf xs 
    in foldr (\(MkSuccess vl prf left), acc => 
               case vl of
                 Nothing  => acc
                 (Just v) => (MkSuccess v prf left)::acc
             ) [] res1

fail : All (Parser a)
fail = MkParser (\_, _ => [])

(<$>) : (a -> b) -> All (Parser a :-> Parser b)
(<$>) f = map f

(<|>) : All (Parser a :-> Parser a :-> Parser a)
(<|>) pa pa' = 
  MkParser (\prf, xs =>
    let 
      res1 = RunParser pa prf xs
    in case res1 of
         [] => RunParser pa' prf xs
         _  => res1
  )

box : All (Parser a :-> Box (Parser a))
box pa = 
  MkBox (\prfLT => 
     MkParser (\prfLTE, xs => 
       RunParser pa (lteTransitive prfLTE (lteSuccLeft prfLT)) xs
  ))

infixl 5 <&>, <&?>, <?&>, &?>>=

(<&>) : Parser a i -> Box (Parser b) i -> Parser (a, b) i
--(<&>) : All (Parser a :-> Box (Parser b) :-> Parser (a, b))
(<&>) pa bpb = MkParser runpab where
  runpab : LTE m i -> Vect m Char -> List (Success (a, b) m)
  runpab prfLTE xs = 
    let 
      resa = RunParser pa prfLTE xs
    in case resa of
         ((MkSuccess va prfLT lefts {Size=sz}) :: []) => 
           let
             pb = call {m=sz} bpb (lteTransitive prfLT prfLTE)
             resb = RunParser pb lteRefl lefts
           in case resb of
                ((MkSuccess vb prf' left') :: [])         => 
                  let 
                    prf1 = lteTransitive (lteSuccRight prf') prfLT
                  in [(MkSuccess (va, vb) prf1 left')]
                _                                         => []
         _         => []

record NEList a where
  constructor MkList
  Head : a
  Tail : List a

mkne : a -> NEList a
mkne a = MkList a []

neadd : a -> NEList a -> NEList a
neadd a (MkList hd tl) = MkList a (hd :: tl)

-- some : All (Parser a) -> All (Parser (NEList a)) --All (Parser (NEList a))
-- some p = fix _ (\rec => (uncurry neadd <$> (p <&> rec)) <|> (mkne <$> p))
 
(<&?>) : Parser a i -> Box (Parser b) i -> Parser (a, Maybe b) i
(<&?>) pa bpb {a} {b} {i} = MkParser runpamb where
  runpamb : LTE m i -> Vect m Char -> List (Success (a, Maybe b) m)
  runpamb prfLTEmi xs = 
    case RunParser pa prfLTEmi xs of
      [(MkSuccess va prfLTszm lefts {Size=sz})] => 
        let
          pb = call {m=sz} bpb (lteTransitive prfLTszm prfLTEmi)
        in case RunParser pb lteRefl lefts of
             [(MkSuccess vb prfb leftb)] => [MkSuccess (va, Just vb) (lteTransitive prfb (lteSuccLeft prfLTszm)) leftb]
             _                           => [MkSuccess (va, Nothing) prfLTszm lefts]
      _   => []

(<?&>) : Parser a i -> Parser b i -> Parser (Maybe a, b) i
(<?&>) pa pb {a} {b} {i} = MkParser runpmab where
  runpmab : LTE m i -> Vect m Char -> List (Success (Maybe a, b) m)
  runpmab prfLTEmi xs = 
    case RunParser pa prfLTEmi xs of
      [(MkSuccess va prfLTszm lefts {Size=sz})] => 
        case RunParser pb (lteTransitive (lteSuccLeft prfLTszm) prfLTEmi) lefts of
          [(MkSuccess vb prfb leftsb)] => [MkSuccess (Just va, vb) (lteTransitive prfb (lteSuccLeft prfLTszm)) leftsb]
          _   => []
      _   => case RunParser pb prfLTEmi xs of
               [(MkSuccess vb prfb leftsb)] => [MkSuccess (Nothing, vb) prfb leftsb]
               _   => []

cons : (a, Maybe (NEList a)) -> NEList a
cons (a, Nothing) = mkne a
cons (a, Just ne) = neadd a ne

some : All(Parser a) -> All(Parser (NEList a))
some p = fix _ (\rec => let r = cons <$> (p <&?> rec) in r)

-- partial
-- some : All (Parser a) -> All (Parser (NEList a))
-- some p = cons <$> (p <&?> box (some p))

(&?>>=) : Parser a i -> (a -> Box (Parser b) i) -> Parser (a, Maybe b) i
(&?>>=) pa k = MkParser runpamb where
  runpamb : LTE m i -> Vect m Char -> List (Success (a, Maybe b) m)
  runpamb ltemi xs = 
    case RunParser pa ltemi xs of
      [(MkSuccess va ltszm lefts {Size=sz})] =>
        let
          bpb = k va
          pb = call {m=sz} bpb $ lteTransitive ltszm ltemi
        in case RunParser pb lteRefl lefts of
             [(MkSuccess vb prf leftsb)] => [MkSuccess (va, Just vb) (lteTransitive prf (lteSuccLeft ltszm)) leftsb]
             _ => [MkSuccess (va, Nothing) ltszm lefts]
      _   => []
 
partial
schainl : Success a i -> Box (Parser (a -> a)) i -> List (Success a i)
-- schainl : Success a i -> Box (Parser (a -> a)) i -> List (Success a i)
schainl {a} s@(MkSuccess va prf left {Size=sz}) bpfa = let p11 = ('a', 1) in res where
  pfa : Parser (a -> a) sz
  pfa = call bpfa prf 
  partial
  res : List (Success a i)
  res = let sf = RunParser pfa lteRefl left
        in 
          case sf of
            [(MkSuccess f prf' lefts' {Size=sz'})] => 
              let
                vfa = f va
                ret = s :: schainl (MkSuccess vfa (lteTransitive (lteSuccRight prf') prf) lefts') bpfa
                arg = bpfa
              in ret
            _   => []

partial
iterate : Parser a i -> Box (Parser (a -> a)) i -> Parser a i
iterate pa bpfai = MkParser runprs where
  partial
  runprs : LTE m i -> Vect m Char -> List (Success a m)
  runprs ltemi xs {m} =
    case RunParser pa ltemi xs of
      [sa@(MkSuccess va prf lefts)] => schainl sa (MkBox (\lt => call bpfai (lteTransitive lt ltemi)))
      _                             => []

hchainl : Parser a i -> Box (Parser (a -> b -> a)) i -> Box (Parser b) i -> Parser a i
hchainl pa bpaba bpb = MkParser rpa where
  rpa : LTE m i -> Vect m Char -> List (Success a m)
  rpa ltemi xs = 
    case RunParser pa ltemi xs of
      [(MkSuccess va ltszm lefts {Size=sz})] => 
        let
          ltszi = lteTransitive ltszm ltemi
          paba = call bpaba ltszi
          pb = call bpb ltszi
        in ?hole
      _   => []
