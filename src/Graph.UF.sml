signature UNION_FIND =
sig
  type set
  
  val set : int -> set
  val find : set * int -> int
  val union : set * int * int -> (int * int) option
end

structure UnionFind :> UNION_FIND =
struct
  datatype state = Root of int | Child of int
  
  type set = state array
  
  fun set n = Array.tabulate (n, fn _ => Root 0)
  fun root (xs, i) =
    case Array.sub (xs, i) of
        Root n => (i, n)
      | Child j =>
        case Array.sub (xs, j) of
            Root n => (j, n)
          | Child k =>
            let in
              Array.update (xs, i, Child k);
              root (xs, k)
            end
  
  val find = #1 o root
  fun union (xs, i, j) =
    let
      val (i, m) = root (xs, i)
      val (j, n) = root (xs, j)
    in
      if i = j then
        NONE
      else
        let
          val (i, j) =
            case Int.compare (m, n) of
                LESS => (j, i)
              | EQUAL => (i, j) before Array.update (xs, i, Root (n+1))
              | GREATER => (i, j)
        in
          Array.update (xs, j, Child i);
          SOME (i, j)
        end
    end
end
