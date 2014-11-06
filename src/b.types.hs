{- Comprobamos que las reglas usuales de la lógica se cumplen en el sistema
   de tipos de Haskell. -}
{- Ejemplos generales -}
identity :: a -> a
identity x = x

const :: a -> (b -> a)
const a = (\b -> a)

proy :: (a,b) -> a
proy (x,y) = x

apply :: ((a->b),a) -> b
apply (f,x) = f(x)


{- Implicación -}
idem :: a -> a
idem x = x

modusPonens :: a -> (a -> b) -> b
modusPonens x f = f x


{- Conjunción -}
conjIntro :: a -> b -> (a,b)
conjIntro x y = (x,y)

fst :: (a,b) -> a
snd :: (a,b) -> b


{- Disyunción -}
disjLeft :: a -> Either a b
disjLeft x = Left x

disjRight :: b -> Either a b
disjRight x = Right x

either :: (a->c) -> (b->c) -> Either a b -> c
either f g (Left x) = f x
either f g (Right y) = g y


{- Falso y verdadero -}
data Falsum
type Not a = a -> Falsum
type Verum = Falsum -> Falsum
exFalsoQuodlibet :: Falsum -> a
