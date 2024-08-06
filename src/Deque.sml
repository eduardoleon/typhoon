signature ATOM_DEQUE =
sig
  type 'a deque
  
  val empty : 'a deque
  val cons : 'a * 'a deque -> 'a deque
  val snoc : 'a deque * 'a -> 'a deque
  val uncons : 'a deque -> ('a * 'a deque) option
  val unsnoc : 'a deque -> ('a deque * 'a) option
end

signature INDEXABLE_DEQUE =
sig
  include ATOM_DEQUE
  
  type 'a hole
  
  val dropL : int * 'a deque -> 'a deque
  val dropR : int * 'a deque -> 'a deque
  val getL : int * 'a deque -> ('a * 'a hole) option
  val getR : int * 'a deque -> ('a * 'a hole) option
  val set : 'a * 'a hole -> 'a deque
end

signature BULK_DEQUE =
sig
  include ATOM_DEQUE
  
  val link : 'a deque * 'a deque -> 'a deque
end
