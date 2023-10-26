functor BootstrappedHeap (structure E : ORDERED) :> HEAP where type elem = E.elem =
struct
  open E
  
  (*  We distinguish between two kinds of heaps:
   *  
   *  - B-heaps (bootstrapped), whose element type is the user-specified one.
   *  - R-heaps (ranked), whose elements are B-heaps.
   *  
   *  Each R-heap has a rank, which is a natural number.  An R-heap of rank n
   *  is also called an n-heap.  R-heaps are inductively defined as follows:
   *  
   *  - A 0-heap consists of just a single element.
   *  - An (n+1)-heap is formed by linking two n-heaps and an optional extra
   *    element.
   *  
   *  Notice that, if xs is an n-heap, then 2^n <= |xs| < 2^(n+1).
   *  
   *  The tail of a B-heap is a list of R-heaps in strictly increasing order
   *  of rank, except possibly for the first two R-heaps, which may have the
   *  same rank.
   *)
  
  datatype heap = ::: of elem * (int * tree) list
       and tree = Tree of heap * heap list * tree list
  
  fun pure x = x ::: nil
  fun head (x ::: _) = x
  fun comp (x ::: _, y ::: _) = x <= y
  
  (*  To link two B-heaps xs and ys, where head xs <= head ys, we insert ys
   *  into xs's tail.  To preserve the invariant on the ranks of the R-heaps
   *  in xs's tail, we proceed as follows:
   *  
   *  - If the first two R-heaps in xs's tail have the same rank, then link
   *    these two R-heaps and add ys as an extra element.
   *  
   *  - Otherwise, create a 0-heap containing ys and add it to xs's tail.
   *)
  
  fun soft (w as Tree (x, xs, ys), y as Tree (z, zs, ws)) =
    if comp (x, z) then Tree (x, xs, y :: ys)
                   else Tree (z, zs, w :: ws)
  
  fun skew (x, Tree (y, xs, ys)) =
    if comp (x, y) then Tree (x, y :: xs, ys)
                   else Tree (y, x :: xs, ys)
  
  fun bump ((p, x) :: (q, y) :: xs) = if p = q then (p + 1, soft (x, y)) :: xs else nil
    | bump _ = nil
  
  fun cons (x, xs) =
    case bump xs of
        nil => (0, Tree (x, nil, nil)) :: xs
      | (p, xs) :: xss => (p, skew (x, xs)) :: xss
  
  fun link (ys as x ::: xss, xs as y ::: yss) =
    if x <= y then x ::: cons (xs, xss)
              else y ::: cons (ys, yss)
  
  (*  To remove the head of a B-heap xs, we must replace it with a new head
   *  taken from xs's tail.
   *)
  
  fun focus ((p, Tree (x, xs, ys)) :: zs, ws) = SOME (p, x, xs, ys, zs, ws)
    | focus _ = NONE
  
  fun next (p, x, xs, ys, zs, ws) = focus (zs, (p, Tree (x, xs, ys)) :: ws)
  
  fun select (xs, NONE) = xs
    | select (xs, SOME ys) =
      if comp (#2 xs, #2 ys) then select (xs, next ys)
                             else select (ys, next ys)
  
  fun retag (_, xs, nil) = xs
    | retag (p, xs, y :: ys) = retag (p - 1, (p, y) :: xs, ys)
  
  fun hard1 (xs, nil) = xs
    | hard1 (xs, (p, y) :: ys) =
      case bump xs of
          nil => hard1 ((p, y) :: xs, ys)
        | xs => hard1 (xs, (p, y) :: ys)
  
  fun hard2 (xs, nil, zs) = hard1 (xs, zs)
    | hard2 (nil, ys, zs) = hard1 (ys, zs)
    | hard2 ((p, x) :: xs, (q, y) :: ys, zs) =
      if Int.<= (p, q) then hard2 (xs, (q, y) :: ys, (p, x) :: zs)
                       else hard2 ((p, x) :: xs, ys, (q, y) :: zs)
  
  fun hard3 (xs, ys, nil, ws) = hard2 (xs, ys, ws)
    | hard3 (xs, nil, zs, ws) = hard2 (xs, zs, ws)
    | hard3 (nil, ys, zs, ws) = hard2 (ys, zs, ws)
    | hard3 ((p, x) :: xs, (q, y) :: ys, (r, z) :: zs, ws) =
      if Int.<= (p, q) andalso Int.<= (p, r) then
        hard3 (xs, (q, y) :: ys, (r, z) :: zs, (p, x) :: ws)
      else if Int.<= (q, r) then
        hard3 ((p, x) :: xs, ys, (r, z) :: zs, (q, y) :: ws)
      else
        hard3 ((p, x) :: xs, (q, y) :: ys, zs, (r, z) :: ws)
  
  fun tail (_ ::: xs) =
    case focus (xs, nil) of
        NONE => NONE
      | SOME xs =>
        let
          val (p, x, xs, ys, zs, ws) = select (xs, next xs)
          val ys = retag (p - 1, zs, ys)
          val ys = foldl cons ys xs
          val x ::: xs = x
        in
          SOME (x ::: hard3 (xs, ys, rev ws, nil))
        end
end
