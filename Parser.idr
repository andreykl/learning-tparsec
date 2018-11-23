module Parser

import Data.Vect

import TypeOperators
import Box
import Success

%default total
%access export

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

infixl 5 <&>, <&?>, <?&>, &?>>=, <&, &>
infixr 4 <$

(<$) : b -> Parser a i -> Parser b i
(<$) f pa = (\_ => f) <$> pa

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

(<&) : Parser a i -> Box (Parser b) i -> Parser a i
(<&) pa bpb = map fst (pa <&> bpb)

(&>) : Parser a i -> Box (Parser b) i -> Parser b i
(&>) pa bpb = map snd (pa <&> bpb)

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

partial
hchainl : Parser a i -> Box (Parser (a -> b -> a)) i -> Box (Parser b) i -> Parser a i
hchainl pa bpaba bpb = 
    let 
      bpaa = (MkBox (\lt => aba'b'aa (call bpaba lt) (call bpb lt)))
    in iterate pa bpaa
  where
    aba'b'aa : Parser (a -> b -> a) i1 -> Parser b i1 -> Parser (a -> a) i1
    aba'b'aa paba pb = MkParser (\ltemn, xs =>
      case RunParser paba ltemn xs of
        [(MkSuccess faba ltszm lefts {Size=sz})] => 
          let
            lteszn = (lteTransitive ltszm ltemn)
          in
            case RunParser pb (lteSuccLeft lteszn) lefts of
              [(MkSuccess vb ltsz'sz lefts' {Size=sz'})] => 
                let
                  ltesz'm = lteTransitive ltsz'sz (lteSuccLeft ltszm)
                in [MkSuccess (\a => faba a vb) ltesz'm lefts']
              _   => []
        _   => [])

satisfy : (p : Char -> Bool) -> Parser Char i
satisfy p = MkParser runpsat where
  runpsat : LTE m i -> Vect m Char -> List (Success Char m)
  runpsat lte xs {m = Z} = []
  runpsat lte (c :: xs) {m = (S k)} = if p c then [MkSuccess c lteRefl xs] else []

satisfies : (p : Char -> Bool) -> Parser (NEList Char) i
satisfies p = some (satisfy p)

char : Char -> Parser Char i
char x = satisfy (== x)

toList : NEList a -> List a
toList (MkList hd tl) = hd :: tl

decimal : Parser Nat i
decimal = MkParser runpdecimal where
  runpdecimal : LTE m i -> Vect m Char -> List (Success Nat m)
  runpdecimal ltemi xs = 
    case RunParser (satisfies isDigit) ltemi xs of
      [(MkSuccess nelist ltszm lefts {Size=sz})] => [MkSuccess (cast $ pack $ toList nelist) ltszm lefts]
      _   => []

