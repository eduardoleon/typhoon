signature ORDERED_KEY =
sig
  type key
  
  val compare : key * key -> order
end

functor SearchSet
  (structure K : ORDERED_KEY
   structure T : SEARCH_TREE) :> SET where type key = K.key =
struct
  open K
  open T
  
  type set = key tree
  type iter_asc = key iter_asc
  type iter_desc = key iter_desc
  
  datatype rest = L of key * key leaf | H of key * key hole
  
  fun loop (k, Leaf xs) = (false, L (k, xs))
    | loop (k, Node xs) =
      case compare (k, #1 xs) of
          LESS => loop (k, left xs)
        | EQUAL => (true, H xs)
        | GREATER => loop (k, right xs)
  
  fun get (k, xs) = loop (k, root xs)
  
  fun set (false, L (_, xs)) = restore xs
    | set (false, H (_, xs)) = delete xs
    | set (true, L xs) = insert xs
    | set (true, H xs) = update xs
end

functor SearchMap
  (structure K : ORDERED_KEY
   structure T : SEARCH_TREE) :> MAP where type key = K.key =
struct
  open K
  open T
  
  type 'a elem = key * 'a
  type 'a map = 'a elem tree
  type 'a iter_asc = 'a elem iter_asc
  type 'a iter_desc = 'a elem iter_desc
  
  datatype 'a rest = L of key * 'a elem leaf | H of key * 'a elem hole
  
  fun loop (k, Leaf xs) = (NONE, L (k, xs))
    | loop (k, Node (xxs as ((k', v), xs))) =
      case compare (k, k') of
          LESS => loop (k, left xxs)
        | EQUAL => (SOME v, H (k', xs))
        | GREATER => loop (k, right xxs)
  
  fun get (k, xs) = loop (k, root xs)
  
  fun set (NONE, L (_, xs)) = restore xs
    | set (NONE, H (_, xs)) = delete xs
    | set (SOME v, L (k, xs)) = insert ((k, v), xs)
    | set (SOME v, H (k, xs)) = update ((k, v), xs)
end
