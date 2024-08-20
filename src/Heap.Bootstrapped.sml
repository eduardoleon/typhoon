functor BootstrappedHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  type elem = E.elem
  
  (*  We distinguish between two kinds of heaps:
   *  
   *  -  B-heaps (bootstrapped) whose element type is the user-specified one.
   *  -  R-heaps (ranked) whose elements are B-heaps.
   *  
   *  Each R-heap has a rank, which is a natural number.  For brevity, R-heaps of rank n
   *  are also called n-heaps.  Then,
   *  
   *  -  The tail of a B-heap is a list of R-heaps in strictly increasing order of rank,
   *     except possibly the first two ones, which may have the same rank.
   *  
   *  -  The tail of an n-heap is a list of R-heaps of ranks n-1, ..., 2, 1, 0.
   *  
   *  -  An n-heap has, in addition to a head and a tail, a neck, which is a list of at
   *     most n B-heaps.
   *  
   *  Notice that, if xs is an n-heap, then 2^n <= |xs| < 2^(n+1).
   *)
  
  datatype heap = ::: of elem * (int * tree) list           (*  B-heap  *)
       and tree = Tree of heap * heap list * tree list      (*  R-heap  *)
  
  fun pure x = x ::: nil
  fun head (x ::: _) = x
  fun comp (x ::: _, y ::: _) = E.<= (x, y)
  
  (*  A 0-heap consists of a single element at the root and nothing else.  *)
  fun zero x = Tree (x, nil, nil)
  
  (*  An (n+1)-heap is built by linking two n-heaps and optionally adding a extra element
   *  to the neck.  This function performs the obligatory linking step, and ought to be
   *  called "succ", for consistency with the previous function.  However, it is more
   *  convenient to use an infix identifier in the code that calls it.
   *)
  fun (w as Tree (x, xs, ys)) ^ (y as Tree (z, zs, ws)) =
    if comp (x, z) then Tree (x, xs, y :: ys)
                   else Tree (z, zs, w :: ws)
  
  (*  This function inserts the optional extra element after linking.  It should only
   *  be used in an expression of the form ̣"x @ a ^ b", where "a" and "b" are known to
   *  have the same rank.  Again, it is convenient to use an infix identifier.
   *)
  fun x @ (Tree (y, xs, ys)) =
    if comp (x, y) then Tree (x, y :: xs, ys)
                   else Tree (y, x :: xs, ys)
  
  (*  This helper function is only necessary because we cannot test whether two integers
   *  are equal during pattern matching.  Otherwise, we would simply write
   *  
   *    fun cons (x, (n,a) :: (n,b) :: xs) = (n + 1, x @ a ^ b) :: xs
   *      | cons (x, xs) = (0, zero x) :: xs
   *)
  fun pair ((m,x) :: (n,y) :: xs) = if m = n then SOME (n, x, y, xs) else NONE
    | pair _ = NONE
  
  (*  To link two B-heaps xs and ys such that "head xs <= head ys", we insert ys into
   *  xs's tail with the following algorithm:
   *  
   *  -  If xs's initial two R-heaps have the same rank, then we link these two R-heaps
   *     and add ys as an extra element.
   *  
   *  -  Otherwise, we insert a new 0-heap containing just ys.
   *)
  fun cons (x ::: xss, xs) =
    case pair xss of
        NONE => x ::: (0, zero xs) :: xss
      | SOME (n, a, b, xss) => x ::: (n + 1, xs @ a ^ b) :: xss
  
  fun link (xs, ys) = if comp (xs, ys) then cons (xs, ys) else cons (ys, xs)
  
  (*  Turning a B-heap's tail into another B-heap is a four-phase operation:
   *  
   *  -  Scan the tail to find the R-heap xs whose head x has the smallest head.  This
   *     phase splits the rest of the tail into a prefix and a suffix.
   *  
   *  -  Reverse prepend xs's tail onto the suffix.  The new suffix begins with R-heaps
   *     of ranks 0, 1, 2, ..., n-1, where n is xs's rank.
   *  
   *  -  Insert each B-heap in xs's neck into the suffix.  If xs's neck has k+1 elements,
   *     then the new suffix begins with R-heaps of ranks k, k, k+1, k+2, ..., n-1.
   *  
   *  -  Merge x's tail with the prefix and the updated suffix.  Notice that the prefix
   *     and suffix are themselves valid B-heap tails, so we will simply say "merging
   *     three B-heap tails" below.
   *)
  
  (*  Unpack the focused R-heap for easier access to its root.  *)
  fun focus ((n, Tree (x, xs, ys)) :: zs, ws) = SOME (n, x, xs, ys, zs, ws)
    | focus _ = NONE
  
  fun next (n, x, xs, ys, zs, ws) = focus (zs, (n, Tree (x, xs, ys)) :: ws)
  
  (*  During the first phase, we compare every subsequent R-tree (ys) against the one
   *  with the smallest root found so far (xs).
   *)
  fun select (xs, NONE) = xs
    | select (xs, SOME ys) =
      if comp (#2 xs, #2 ys) then select (xs, next ys)
                             else select (ys, next ys)
  
  (*  During the second phase, we tag the each child (y) of the focused R-heap with
   *  its rank before prepending it to the suffix (xs).
   *)
  fun retag (_, xs, nil) = xs
    | retag (n, xs, y :: ys) = retag (n - 1, (n - 1, y) :: xs, ys)
  
  (*  During most of the third phase, the suffix (xs) begins with two R-heaps of the
   *  same rank, so we link them and add the next B-heap (y) as an extra element.
   *)
  fun recons ((n,a) :: (_,b) :: xs, y :: ys) = recons ((n + 1, y @ a ^ b) :: xs, ys)
    | recons (xs, _) = xs
  
  (*  When the third phase begins, the suffix (xs) does not begin with two R-heaps of
   *  the same rank, so we insert the the first B-heap (y) as a standalone 0-heap.
   *)
  fun cons (xs, y :: ys) = recons ((0, zero y) :: xs, ys)
    | cons (xs, nil) = xs
  
  (*  Merging three B-heap tails is itself a three-phase operation:
   *  
   *  -  Visit the R-heaps in all three tails in increasing order of rank, and shift
   *     them into a temporary list until one tail dies (is empty).
   *  
   *  -  Visit the R-heaps in both surviving tails in increasing order of rank, and
   *     shift them into the same temporary list until one more tail dies.
   *  
   *  -  Shift the temporary list's R-heaps back into the surviving tail.
   *)
  
  (*  Ensure the tail contains no two R-heaps of the same rank.  *)
  fun compact xs =
    case pair xs of
        NONE => xs
      | SOME (n, a, b, xs) => compact ((n + 1, a ^ b) :: xs)
  
  (*  During the third phase, we must compact the tail (see above) before prepending
   *  the next R-heap from the temporary list.
   *)
  fun restore (xs, nil) = xs
    | restore (xs, y :: ys) = restore (y :: compact xs, ys)
  
  (*  During the second phase, we collect R-heaps from two nonempty tails.  *)
  fun merge2 (xs, nil, zs) = restore (xs, zs)
    | merge2 (nil, ys, zs) = restore (ys, zs)
    | merge2 ((m, x) :: xs, (n, y) :: ys, zs) =
      if m <= n then merge2 (xs, (n, y) :: ys, (m, x) :: zs)
                else merge2 ((m, x) :: xs, ys, (n, y) :: zs)
  
  (*  During the first phase, we collect R-heaps from three nonempty tails.  *)
  fun merge3 (xs, ys, nil, ws) = merge2 (xs, ys, ws)
    | merge3 (xs, nil, zs, ws) = merge2 (xs, zs, ws)
    | merge3 (nil, ys, zs, ws) = merge2 (ys, zs, ws)
    | merge3 ((m, x) :: xs, (n, y) :: ys, (p, z) :: zs, ws) =                   
      if m <= n andalso m <= p then
        merge3 (xs, (n, y) :: ys, (p, z) :: zs, (m, x) :: ws)
      else if n <= p then
        merge3 ((m, x) :: xs, ys, (p, z) :: zs, (n, y) :: ws)
      else
        merge3 ((m, x) :: xs, (n, y) :: ys, zs, (p, z) :: ws)
  
  fun tail (_ ::: xs) =
    case focus (xs, nil) of
        NONE => NONE
      | SOME xs =>
        let
          val (n, x, xs, ys, zs, ws) = select (xs, next xs)             (*  First  *)
          val zs = retag (n, zs, ys)                                    (*  Second  *)
          val zs = cons (zs, xs)                                        (*  Third  *)
          val x ::: xs = x
        in
          SOME (x ::: merge3 (xs, zs, rev ws, nil))                     (*  Fourth  *)
        end
end
