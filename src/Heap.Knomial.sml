functor KnomialHeapList (val base : int) :> HEAP_LIST =
struct
  open Compare
  open Rank
  
  datatype 'a tree = ::: of 'a * 'a tree list list
  
  fun pure x = x ::: nil
  fun soft (x ::: xss, xs) = x ::: xs :: xss
  
  type 'a list = 'a tree rank list
  
  val empty = nil
  
  (*  This should actually be a nested functor member.  *)
  fun ops op<= =
    let
      fun comp (x ::: _, y ::: _) = x <= y
      val op^ = soft o bubble (swap comp)
      
      fun norm (p, x, xs) =
        case untag (base, p, x, xs) of
            NONE => (p, x) :: xs
          | SOME (p, x, xs, xss) => norm (1 + p, x ^ xs, xss)
      
      fun restore (xs, nil) = xs
        | restore (xs, (p, x) :: ys) = restore (norm (p, x, xs), ys)
      
      fun cons (x, xs) = norm (0, pure x, xs)
      val link = restore o collect
      
      fun unfocus (p, x ::: xs, ys, zs) =
        let
          val xs = retag' (p, xs)
          val ys = List.revAppend (zs, ys)
        in
          (x, link (xs, ys))
        end
      
      val uncons = Option.map (unfocus o locate comp) o first
    in
      { cons = cons, link = link, uncons = uncons }
    end
end
