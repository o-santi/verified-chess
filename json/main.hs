import qualified Data.ByteString as B
import Data.Word (Word8)
import Data.Text.Encoding (decodeUtf8')
import Data.Bits
import qualified Utf8 as U

byte_to_word :: U.Byte -> Word8
byte_to_word byte =
  let set b i = case b of { U.True -> bit i; U.False -> zeroBits } in
    case (U.to_bits byte) of { U.Pair b0 (U.Pair b1 (U.Pair b2 (U.Pair b3 (U.Pair b4 (U.Pair b5 (U.Pair b6 b7)))))) ->
                                                                                                                    (set b0 0) .|. (set b1 1) .|. (set b2 2) .|. (set b3 3) .|. (set b4 4) .|. (set b5 5) .|. (set b6 6) .|. (set b7 7) }
    

word_to_byte :: Word8 -> U.Byte
word_to_byte word =
  let
    b i = if testBit word i then U.True else U.False
    bits = U.Pair (b 0) (U.Pair (b 1) (U.Pair (b 2) (U.Pair (b 3) (U.Pair (b 4) (U.Pair (b 5) (U.Pair (b 6) (b 7))))))) in U.of_bits bits

byte_string_to_byte_list :: B.ByteString -> U.List U.Byte
byte_string_to_byte_list = B.foldl (\l w -> U.Cons (word_to_byte w) l) U.Nil

convert_list :: [a] -> U.List a -> [a]
convert_list acc U.Nil = acc
convert_list acc (U.Cons h rest) = (convert_list (h: acc) rest) 

main :: IO ()
main = do
  contents <- B.readFile "json.v"
  let bytes = U.utf8_decode (byte_string_to_byte_list contents) in
    case bytes of { U.Ok (U.Pair val rest) ->
      let bs = map byte_to_word $ convert_list [] (U.utf8_encode (val))
      in print (decodeUtf8' (B.pack bs));
          U.Err (errs) -> print errs }
