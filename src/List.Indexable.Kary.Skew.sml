functor SkewKaryList (val base : int) :> INDEXABLE_LIST =
struct
  open Rank
  
  datatype 'a tree = ::: of 'a * 'a tree list
  datatype 'a step = Elem of 'a | Tree of 'a tree rank
  
  type 'a hole = 'a tree rank list * 'a step list
  type 'a list = 'a tree rank list
  
  val empty = nil
  fun cons (x, xs) =
    case untag' (base, xs) of
        NONE => (1, x ::: nil) :: xs
      | SOME (p, xs, xss, xsss) => (1 + p * base, x ::: xs :: xss) :: xsss
  
  fun uncons nil = NONE
    | uncons ((p, x ::: xs) :: xss) = SOME (x, retag (p div base, xs, xss))
  
  fun drop (_, nil) = nil
    | drop (n, xxs as (p, _ ::: x) :: xs) =
      case Interval.cutoff (n, 1 :: p :: nil) of
          0 => xxs
        | 1 => drop (n - 1, retag (p div base, x, xs))
        | _ => drop (n - p, xs)
  
  fun loop (_, nil, _) = NONE
    | loop (n, (p, x ::: xs) :: xss, ss) =
      case Interval.cutoff (n, 1 :: p :: nil) of
          0 => SOME (x, (retag (p div base, xs, xss), ss))
        | 1 => loop (n - 1, retag (p div base, xs, xss), Elem x :: ss)
        | _ => loop (n - p, xss, Tree (p, x ::: xs) :: ss)
  
  fun get (n, xs) = if n >= 0 then loop (n, xs, nil) else NONE
  
  fun loop (xs, nil) = xs
    | loop (xs, Elem x :: ss) = loop (cons (x, xs), ss)
    | loop (xs, Tree x :: ss) = loop (x :: xs, ss)
  
  fun set (x, (xs, ss)) = loop (xs, Elem x :: ss)
  fun trunc (xs, _) = xs
end
