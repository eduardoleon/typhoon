signature BIT_VECTOR_KEY =
sig
  type key
  
  datatype order = Equal | Less of int | Greater of int
  
  val sub : key * int -> bool
  val compare : key * key -> order
end

functor CritBitSet (K : BIT_VECTOR_KEY) :> SET where type key = K.key =
struct
  open K
  open CritBitTree
  
  type set = key tree option
  type rest = key * key leaf
  
  val empty = NONE
  fun next (k, xs) = if sub (k, index xs) then right xs else left xs
  
  fun loop (k, Node xs) = loop (k, next (k, xs))
    | loop (k, Leaf (x, xs)) =
      case compare (k, x) of
          Equal => (true, (x, xs))
        | Less n => (false, (k, insleft (n, pure x, xs)))
        | Greater n => (false, (k, insright (n, pure x, xs)))
  
  fun get (k, SOME xs) = loop (k, root xs)
    | get (k, NONE) = (false, (k, CritBitTree.empty))
  
  fun set (false, (_, xs)) = delete xs
    | set (true, (x, xs)) = SOME (update (pure x, xs))
end

functor CritBitMap (K : BIT_VECTOR_KEY) :> MAP where type key = K.key =
struct
  open K
  open CritBitTree
  
  type 'a elem = key * 'a
  type 'a rest = key * 'a elem leaf
  type 'a map = 'a elem tree option
  
  val empty = NONE
  fun next (k, xs) = if sub (k, index xs) then right xs else left xs
  
  fun loop (k, Node xs) = loop (k, next (k, xs))
    | loop (k, Leaf (x as (k', v), xs)) =
      case compare (k, k') of
          Equal => (SOME v, (k', xs))
        | Less n => (NONE, (k, insleft (n, pure x, xs)))
        | Greater n => (NONE, (k, insright (n, pure x, xs)))
  
  fun get (k, SOME xs) = loop (k, root xs)
    | get (k, NONE) = (NONE, (k, CritBitTree.empty))
  
  fun set (NONE, (_, xs)) = delete xs
    | set (SOME v, (k, xs)) = SOME (update (pure (k, v), xs))
end
