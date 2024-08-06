structure StringKey : VECTOR_KEY =
struct
  open Substring
  
  type key = string
  
  datatype order = Equal | Less of int | Greater of int
  
  fun sub (xs, n) =
    let
      val char = String.sub (xs, n div 8)
      val mask = Word8.>> (0wx80, Word.fromInt (n mod 8))
    in
      Word8.andb (mask, Byte.charToByte char)
    end
    handle Substring => 0wx0
  
  fun inByte (n, mask, byte, diff) =
    case Word8.andb (mask, diff) of
        0wx0 => inByte (n + 1, Word8.>> (mask, 0wx1), byte, diff)
      | _ =>
        case Word8.andb (mask, byte) of
            0wx0 => Less n
          | _ => Greater n
  
  fun inString (n, SOME (x, xs), SOME (y, ys)) =
      let
        val byte1 = Byte.charToByte x
        val byte2 = Byte.charToByte y
      in
        case Word8.xorb (byte1, byte2) of
            0wx0 => inString (n + 8, getc xs, getc ys)
          | diff => inByte (n, 0wx80, byte1, diff)
      end
    | inString _ = Equal
  
  fun compare (xs, ys) = inString (0, getc (full xs), getc (full ys))
end
