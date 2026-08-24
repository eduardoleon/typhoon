functor SkewBinomialHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  type elem = E.elem
  
  datatype 'a tree = Tree of 'a * 'a list * 'a tree list
  
  datatype heap = ::: of elem * (int * heap tree) list
  
  fun pure x = x ::: nil
  fun head (x ::: _) = x
  fun comp (x ::: _, y ::: _) = E.<= (x, y)
  
  fun zero x = Tree (x, nil, nil)
  
  fun (w as Tree (x, xs, ys)) ^ (y as Tree (z, zs, ws)) =
    if comp (x, z) then Tree (x, xs, y :: ys)
                   else Tree (z, zs, w :: ws)
  
  fun x @ (Tree (y, xs, ys)) =
    if comp (x, y) then Tree (x, y :: xs, ys)
                   else Tree (y, x :: xs, ys)
  
  (*  This helper function only exists because we cannot test whether two integers
   *  are equal during pattern matching.  Otherwise, we would write
   *  
   *    fun cons (x, (n,a) :: (n,b) :: xs) = (n + 1, x @ a ^ b) :: xs
   *      | cons (x, xs) = (0, zero x) :: xs
   *    
   *    fun compact ((n,a) :: (n,b) :: xs) = compact ((n + 1, a ^ b) :: xs)
   *      | compact xs = xs
   *)
  fun pair ((m,x) :: (n,y) :: xs) = if m = n then SOME (n, x, y, xs) else NONE
    | pair _ = NONE
  
  fun cons (x ::: xss, xs) =
    case pair xss of
        NONE => x ::: (0, zero xs) :: xss
      | SOME (n, ys, zs, xss) => x ::: (n + 1, xs @ ys ^ zs) :: xss
  
  fun link (xs, ys) = if comp (xs, ys) then cons (xs, ys) else cons (ys, xs)
  
  (*  To discard the minimum element of a heap, we must turn the heap's tail into
   *  another heap.  This operation has three phases.
   *)
  
  (*  PHASE 1:  Find the minimum tree and remove it from the tail.  This splits
   *  the rest of the tail into a prefix and a suffix.
   *)
  fun focus ((n, x) :: xs, ys) = SOME (n, x, xs, ys)
    | focus _ = NONE
  
  fun root (_, Tree (x, _, _), _, _) = x
  fun next (n, x, xs, ys) = focus (xs, (n, x) :: ys)
  
  fun select (xs, NONE) = xs
    | select (xs, SOME ys) =
      if comp (root xs, root ys) then select (xs, next ys)
                                 else select (ys, next ys)
  
  (*  PHASE 2:  Split the minimum tree into root, children and extra elements, and
   *  move the children and extra elements into the suffix.
   *)
  fun children (_, xs, nil) = xs
    | children (n, xs, y :: ys) = children (n - 1, (n - 1, y) :: xs, ys)
  
  fun extras ((n,a) :: (_,b) :: xs, y :: ys) = extras ((n + 1, y @ a ^ b) :: xs, ys)
    | extras (xs, _) = xs
  
  fun extra (xs, y :: ys) = extras ((0, zero y) :: xs, ys)
    | extra (xs, nil) = xs
  
  (*  PHASE 3:  Split the minimum tree's root into head and tail, and merge the tail
   *  with the prefix and the updated suffix.
   *)
  fun compact xs =
    case pair xs of
        NONE => xs
      | SOME (n, x, y, xs) => compact ((n + 1, x ^ y) :: xs)
  
  fun merge1 (xs, nil) = xs
    | merge1 (xs, y :: ys) = merge1 (y :: compact xs, ys)
  
  fun merge2 (xs, nil, zs) = merge1 (xs, zs)
    | merge2 (nil, ys, zs) = merge1 (ys, zs)
    | merge2 ((m, x) :: xs, (n, y) :: ys, zs) =
      if m <= n then merge2 (xs, (n, y) :: ys, (m, x) :: zs)
                else merge2 ((m, x) :: xs, ys, (n, y) :: zs)
  
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
  
  (*  Finally, we put everything together.  *)
  fun tail (_ ::: xs) =
    case focus (xs, nil) of
        NONE => NONE
      | SOME xs =>
        let
          (*  Phase 1  *)
          val (n, x, xs, ys) = select (xs, next xs)
          
          (*  Phase 2  *)
          val Tree (z, zs, ws) = x
          val xs = children (n, xs, ws)
          val xs = extra (xs, zs)
          
          (*  Phase 3  *)
          val z ::: zs = z
          val zs = merge3 (zs, xs, rev ys, nil)
        in
          SOME (z ::: zs)
        end
end
