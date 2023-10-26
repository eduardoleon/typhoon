structure BytesKey : VECTOR_KEY =
struct
  open Word8VectorSlice
  
  type key = vector
  
  datatype order = Equal | Less of int | Greater of int
  
  fun sub (xs, n) =
    let
      val byte = Word8Vector.sub (xs, n div 8)
      val mask = Word8.<< (0wx1, Word.fromInt (n mod 8))
    in
      Word8.andb (mask, byte)
    end
    handle Substring => 0wx0
  
  fun inByte (n, mask, byte, diff) =
    case Word8.andb (mask, diff) of
        0wx0 => inByte (n + 1, Word8.<< (mask, 0wx1), byte, diff)
      | _ =>
        case Word8.andb (mask, byte) of
            0wx0 => Less n
          | _ => Greater n
  
  fun inVector (n, SOME (x, xs), SOME (y, ys)) =
      (case Word8.xorb (x, y) of
           0wx0 => inVector (n + 8, getItem xs, getItem ys)
         | diff => inByte (n, 0wx1, x, diff))
    | inVector _ = Equal
  
  fun compare (xs, ys) = inVector (0, getItem (full xs), getItem (full ys))
end
