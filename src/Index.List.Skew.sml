structure SkewBinaryList :> INDEXABLE_LIST =
struct
  datatype 'a tree = Leaf of 'a | Node of 'a * 'a tree * 'a tree
  
  type 'a list = (int * 'a tree) list
  type 'a hole = 'a list * 'a list
  
  val empty = nil
  
  (*  This helper function only exists because we cannot test whether two integers
   *  are equal during pattern matching.  Otherwise, we would write
   *  
   *    fun cons (x, (n,a) :: (n,b) :: xs) = (2*n + 1, Node (x,a,b)) :: xs
   *      | cons (x, xs) = (1, zero x) :: xs
   *)
  fun pair ((m,x) :: (n,y) :: xs) = if m = n then SOME (n, x, y, xs) else NONE
    | pair _ = NONE
  
  fun cons (x, xs) =
    case pair xs of
        NONE => (1, Leaf x) :: xs
      | SOME (n, a, b, xs) => (2*n + 1, Node (x,a,b)) :: xs
  
  fun uncons nil = NONE
    | uncons ((_, Leaf x) :: xs) = SOME (x, xs)
    | uncons ((n, Node (x,a,b)) :: xs) = SOME (x, (n div 2, a) :: (n div 2, b) :: xs)
  
  fun loop (0, xs) = xs
    | loop (_, nil) = nil
    | loop (m, (_, Leaf _) :: xs) = loop (m - 1, xs)
    | loop (m, (n, Node (_,a,b)) :: xs) =
      if m >= n then
        loop (m - n, xs)
      else
        loop (m - 1, (n div 2, a) :: (n div 2, b) :: xs)
  
  fun drop (n, xs) = if n >= 0 then loop (n, xs) else xs
  
  fun loop (_, nil, _) = NONE
    | loop (0, (_, Leaf x) :: xs, ys) = SOME (x, (xs, ys))
    | loop (m, (_, Leaf x) :: xs, ys) = loop (m - 1, xs, (1, Leaf x) :: ys)
    | loop (m, (y as (n, Node (x,a,b))) :: xs, ys) =
      if m >= n then
        loop (m - n, xs, y :: ys)
      else
        loop (m, (1, Leaf x) :: (n div 2, a) :: (n div 2, b) :: xs, ys)
  
  fun get (n, xs) = if n >= 0 then loop (n, xs, nil) else NONE
  
  fun loop (xs, (_, Leaf x) :: ys) = loop (cons (x, xs), ys)
    | loop (xs, y :: ys) = loop (y :: xs, ys)
    | loop (xs, nil) = xs
  
  fun set (x, (xs, ys)) = loop (cons (x, xs), ys)
end
