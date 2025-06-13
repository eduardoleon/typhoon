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
  
  datatype rest = L of key * key leaf | H of key * key hole
  
  fun loop (k, Leaf xs) = Leaf xs
    | loop (k, Node xs) =
      case compare (k, #1 xs) of
          LESS => loop (k, left xs)
        | EQUAL => Node xs
        | GREATER => loop (k, right xs)
  
  fun get (k, xs) =
    case loop (k, root xs) of
        Leaf xs => (false, L (k, xs))
      | Node xs => (true, H xs)
  
  fun set (false, L (_, xs)) = splay xs
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
  
  datatype 'a rest = L of key * 'a elem leaf | H of key * 'a elem hole
  
  fun loop (_, Leaf xs) = Leaf xs
    | loop (k, Node xs) =
      case compare (k, #1 (#1 xs)) of
          LESS => loop (k, left xs)
        | EQUAL => Node xs
        | GREATER => loop (k, right xs)
  
  fun get (k, xs) =
    case loop (k, root xs) of
        Leaf xs => (NONE, L (k, xs))
      | Node ((k, v), xs) => (SOME v, H (k, xs))
  
  fun set (NONE, L (_, xs)) = splay xs
    | set (NONE, H (_, xs)) = delete xs
    | set (SOME v, L (k, xs)) = insert ((k, v), xs)
    | set (SOME v, H (k, xs)) = update ((k, v), xs)
end
