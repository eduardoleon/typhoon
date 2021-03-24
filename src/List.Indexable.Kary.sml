functor KaryList (val base : int) :> INDEXABLE_LIST =
struct
  open Rank
  
  datatype 'a tree = Pure of 'a | Many of 'a tree list
  
  type 'a hole = 'a tree rank list * 'a tree rank list
  type 'a list = 'a tree rank list
  
  fun norm (p, x, xs) =
    case untag (base, p, x, xs) of
        NONE => (p, x) :: xs
      | SOME (p, x, xs, xss) => norm (p * base, Many (x :: xs), xss)
  
  val empty = nil
  fun cons (x, xs) = norm (1, Pure x, xs)
  fun uncons nil = NONE
    | uncons ((_, Pure x) :: xs) = SOME (x, xs)
    | uncons ((p, Many x) :: xs) = uncons (retag (p div base, x, xs))
  
  fun drop (_, nil) = nil
    | drop (n, xxs as (p, x) :: xs) =
      case (n < p, x) of
          (true, Pure _) => xxs
        | (true, Many x) => drop (n, retag (p div base, x, xs))
        | _ => drop (n - p, xs)
  
  fun loop (_, nil, _) = NONE
    | loop (n, (p, x) :: xs, ys) =
      case (n < p, x) of
          (true, Pure x) => SOME (x, (xs, ys))
        | (true, Many x) => loop (n, retag (p div base, x, xs), ys)
        | _ => loop (n - p, xs, (p, x) :: ys)
  
  fun get (n, xs) = if n >= 0 then loop (n, xs, nil) else NONE
  
  fun loop (xs, nil) = xs
    | loop (xs, (p, y) :: ys) = loop (norm (p, y, xs), ys)
  
  fun set (x, (xs, ys)) = loop (cons (x, xs), ys)
  fun trunc (xs, _) = xs
end
