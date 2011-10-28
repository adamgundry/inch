This module (which is not inch-friendly) exists to rename some
functions, getting around the lack of support for typeclasses. Maybe I
should just bite the bullet and implement typeclasses.


> module UnitsHacks where

> plusRational :: Rational -> Rational -> Rational
> plusRational = (+)

> minusRational :: Rational -> Rational -> Rational
> minusRational = (-)

> timesRational :: Rational -> Rational -> Rational
> timesRational = (*)

> recipRational :: Rational -> Rational
> recipRational = recip

> powRational :: Rational -> Integer -> Rational
> powRational = (^)