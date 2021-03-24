functor SkewKnomialHeapList (val base : int) :> HEAP_LIST =
struct
  open Compare
  open Rank
  
  datatype 'a tree = Tree of 'a * 'a list * 'a tree list list
  
  fun pure x = Tree (x, nil, nil)
  fun soft (Tree (x, xs, ys), y) = Tree (x, xs, y :: ys)
  
  type 'a list = 'a tree rank list
  
  val empty = nil
  
  (*  This should actually be a nested functor member.  *)
  fun ops op<= =
    let
      fun comp (Tree (x, _, _), Tree (y, _, _)) = x <= y
      val op^ = soft o bubble (swap comp)
      
      fun cons (x, xs) =
        case untag' (base, xs) of
            NONE => (0, pure x) :: nil
          | SOME (p, y, ys, xs) =>
            let
              val Tree (y, ys, zs) = y ^ ys
              val (x, y) = swap op<= (x, y)
            in
              (1 + p, Tree (x, y :: ys, zs)) :: xs
            end
      
      fun norm (p, x, xs) =
        case untag (base, p, x, xs) of
            NONE => (p, x) :: xs
          | SOME (p, x, xs, xss) => norm (1 + p, x ^ xs, xss)
      
      fun restore (xs, nil) = xs
        | restore (xs, (p, x) :: ys) = restore (norm (p, x, xs), ys)
      
      fun link args =
        case collect args of
            ((p, x) :: xs, ys) => restore (norm (p, x, xs), ys)
          | _ => nil
      
      fun unfocus (p, Tree (x, xs, xss), ys, zs) =
        let
          val xs = foldl cons (retag' (p, xss)) xs
          val ys = List.revAppend (zs, ys)
        in
          (x, link (xs, ys))
        end
      
      val uncons = Option.map (unfocus o locate comp) o first
    in
      { cons = cons, link = link, uncons = uncons }
    end
end
