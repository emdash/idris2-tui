-- BSD 3-Clause License
--
-- Copyright (c) 2023, Brandon Lewis
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
-- 1. Redistributions of source code must retain the above copyright notice, this
--    list of conditions and the following disclaimer.
--
-- 2. Redistributions in binary form must reproduce the above copyright notice,
--    this list of conditions and the following disclaimer in the documentation
--    and/or other materials provided with the distribution.
--
-- 3. Neither the name of the copyright holder nor the names of its
--    contributors may be used to endorse or promote products derived from
--    this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


||| Candidates for Upstream Contributions
|||
||| For a definition to live here it must be sufficiently general that
||| it would ideally live somewhere upstream (e.g. the standard
||| library, prelude, or another some other project).
|||
||| Definitions should be namespaced within this file according to how
||| they would be imported if they existed upstream. E.g., a function
||| on strings intended for the standard library should live in a
||| namespace called `Data.String' in this file.
module TUI.Util


import Data.Fin
import Data.SnocList
import Data.String
import Data.SortedMap
import Data.Vect
import Data.Vect.Quantifiers


%default total


namespace Data.String
  ||| Truncate a string to the given length.
  public export
  truncateTo : Nat -> String -> String
  truncateTo n s = pack $ take n $ unpack s

  ||| Format a string into an exact width
  |||
  ||| Pad if length is shorter than width, truncate if longer.
  public export
  frameString : Nat -> String -> String
  frameString w s =
    let l = length s
    in case (l < length s) of
      True  => padRight w ' ' s
      False => truncateTo w s

  ||| Append a single character to the given string
  public export
  append : Char -> String -> String
  append char self = self ++ singleton char

namespace Data.Either
  ||| XXX: should be library function
  export partial
  unwrapLeft : Either a b -> a
  unwrapLeft (Left x) = x

  ||| XXX: should be library function
  export partial
  unwrapRight: Either a b -> b
  unwrapRight (Right y) = y

  ||| XXX: should be a library function
  export
  fromMaybe : e -> Maybe a -> Either e a
  fromMaybe err Nothing         = Left  err
  fromMaybe err (Just whatever) = Right whatever


namespace Data.SortedMap
  -- xxx: this needs to be more generic.
  export
  foldDict : Eq a => Ord a => a  -> Nat -> SortedMap a Nat -> SortedMap a Nat
  foldDict k v accum = case SortedMap.lookup k accum of
    Nothing => insert k v       accum
    Just x  => insert k (v + x) accum

  ||| Create the reverse mapping for a given dictionary.
  |||
  ||| Elements are appended to a list, in case the mapping isn't 1:1.
  |||
  ||| XXX: generalize to `transposeWith`, uses a function which to
  |||      fold elements sharing the same key in the input dict.
  ||| XXX: move me to a utils library.
  ||| XXX: Potentially contribute this upstream to the containers library.
  export
  transpose
    :  Eq a
    => Eq b
    => Ord a
    => Ord b
    => SortedMap a b
    -> SortedMap b (List a)
  transpose dict =
    -- XXX: I spent way too much time trying to do this without creating
    -- an intermediate list. How to avoid this?
    let swapped = map swap (SortedMap.toList dict)
    in foldl foldIn empty swapped
  where
    foldIn : SortedMap b (List a) -> (b, a) -> SortedMap b (List a)
    foldIn accum (k, v) = case lookup k accum of
      Nothing => SortedMap.insert k [v]       accum
      Just vs => SortedMap.insert k (v :: vs) accum


namespace Data.SnocList
  ||| `unpack`, but for SnocLists
  public export
  kcapnu : String -> SnocList Char
  kcapnu s = cast $ unpack s

  ||| `pack`, but for SnocLists
  public export
  kcap : SnocList Char -> String
  kcap s = pack $ cast s

  ||| `tail` for SnocList
  public export
  liat : SnocList a -> SnocList a
  liat [<] = [<]
  liat (xs :< x) = xs

  ||| `head` for SnocList
  public export
  daeh : SnocList a -> Maybe a
  daeh [<] = Nothing
  daeh (xs :< x) = Just x

  ||| Return the tail part of a regular list.
  public export
  tail : List a -> List a
  tail [] = []
  tail (x :: xs) = xs


namespace Data.List

  ||| Update the given list at index `i` by the application of `f`.
  public export
  updateAt
    :  (f : a -> a)
    -> (l : List a)
    -> (i : Fin (length l))
    -> List a
  updateAt f (x :: xs) FZ     = f x :: xs
  updateAt f (x :: xs) (FS i) =   x :: updateAt f xs i


namespace Data.Fin
  ||| Decrement the given `Fin` without changing the bound.
  |||
  ||| Wraps around to `last` when applied to `FZ`, mirroring the
  ||| behavior of `finS`, which wraps around to `FZ` when applied to
  ||| `last`.
  |||
  ||| XXX: rename to `finPred`. `predS` is nonsense.
  public export
  predS : {n : Nat} -> Fin n -> Fin n
  predS FZ     = last
  predS (FS k) = weaken k


namespace Data.Nat
  ||| The absolute value of the difference between two Nats
  public export
  diff : Nat -> Nat -> Nat
  diff a b = case a < b of
    True  => b `minus` a
    False => a `minus` b

namespace Data.Integer
  ||| Same as above, but the operands are integers.
  public export
  diff : Integer -> Integer -> Nat
  diff a b = integerToNat $ abs $ a - b

namespace Data.Vect.Quantifiers
  ||| Map a function over a heterogenous vector.
  |||
  ||| Unlike mapProperty, the result is homogenous vector. This is
  ||| useful for extracting properties which don't vary with index
  ||| type.
  public export
  mapAll
    :  {k : Nat}
    -> {xs : Vect k a}
    -> (f : forall x. p x -> y)
    -> All p xs
    -> Vect k y
  mapAll f xs = forget $ mapProperty f xs

  ||| Fold over a heterogenous vector.
  |||
  ||| The result is collected into a single value.
  ||| f : map each generic value into a single concrete value
  ||| g : accumulate concrete values into a single result.
  public export
  reduceAll
    :  {k : Nat}
    -> {xs : Vect k a}
    -> (g : y -> y -> y)
    -> (f : forall x. p x -> y)
    -> y
    -> All p xs
    -> y
  reduceAll g f accum [] = accum
  reduceAll g f accum (x :: xs) = reduceAll g f (g accum (f x)) xs

  ||| Update the value at the index, without changing the type.
  public export
  updateAt
    :  {k : Nat}
    -> {xs : Vect k a}
    -> (i : Fin k)
    -> (f : forall x. p x -> p x)
    -> All p xs
    -> All p xs
  updateAt FZ     f (x :: xs) = f x :: xs
  updateAt (FS i) f (x :: xs) = x :: updateAt i f xs

  ||| Update the value at the index, without changing the type.
  public export
  replaceAt
    :  {k : Nat}
    -> {xs : Vect k Type}
    -> (i : Fin k)
    -> (value : p (index i xs))
    -> All p xs
    -> All p xs
  replaceAt FZ     v (_ :: xs) = v :: xs
  replaceAt (FS i) v (y :: xs) = y :: replaceAt i v xs

  ||| get the value at the index
  public export
  get
    :  {k : Nat}
    -> {xs : Vect k Type}
    -> (i : Fin k)
    -> All p xs
    -> p (index i xs)
  get FZ     (x :: xs) = x
  get (FS i) (x :: xs) = get i xs

  -- thanks to @Hreyfill and @Red Krow
  --
  -- see discord msgs:
  -- https://discord.com/channels/827106007712661524/834611018775789568/1302304642897678397
  -- https://discord.com/channels/827106007712661524/834611018775789568/1302323106286800940

  ||| A type-level helper function used in the signature of `happly`
  |||
  ||| This essentially folds over the argument list with `->`,
  ||| converting `[Foo, Bar, Baz] Quux` into `Foo -> Bar -> Baz ->
  ||| Quux`.
  public export
  0 HFunc : (inputs : Vect k Type) -> (return : Type) -> Type
  HFunc []            return = return
  HFunc (arg :: args) return = arg -> (HFunc args) return

  ||| Apply an HVect to a function which matches the given type.
  |||
  ||| This is useful for form validation, to convert a generic HList
  ||| to an application-specific record type.
  public export
  happly
    :  {0 args : Vect k Type}
    -> (HFunc args return)
    -> HVect args
    -> return
  happly const [] = const
  happly func  (arg :: args) = happly (func arg) args

  ||| Convert an HVect of Maybes to a Maybe (HVect)
  export
  allIsJust : All Maybe a -> Maybe (HVect a)
  allIsJust [] = Just []
  allIsJust ((Just x) :: xs) = (x ::) <$> allIsJust xs
  allIsJust (Nothing  :: xs) = Nothing
