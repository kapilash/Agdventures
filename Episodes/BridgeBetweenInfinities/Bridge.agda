module Bridge where


open import Data.Bool using (Bool; true; false; _∧_; _∨_; _xor_; T )
open import Data.Vec using (Vec; []; _∷_ ; _∷ʳ_ ; zipWith; take; drop; replicate; map ; toList)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ ; +-suc)
open import Data.Integer using (ℤ)
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; _<+>_ ) renaming (fromVec to strFromVec ; concat to concatStr;  _++_ to strappend)
open import Data.Char using (Char)

open import Data.List renaming (zipWith to zipWithList ; take to takeFromList ; drop to dropFromList ; replicate to replicateList ; map to mapList) hiding ( _∷ʳ_ )



Bit = Bool
Byte = Vec Bit 8
Chunk = Vec Bit 7


data ZigZag : Set where
  zig : ℕ → ZigZag
  zag : ℕ → ZigZag

ℤ→ZigZag : ℤ → ZigZag
ℤ→ZigZag (ℤ.pos n) = zig n
ℤ→ZigZag (ℤ.negsuc n) = zag n

ZigZag→ℤ : ZigZag → ℤ
ZigZag→ℤ (zig x) = ℤ.pos x
ZigZag→ℤ (zag x) = ℤ.negsuc x

iso-encode-decode : ∀ (z : ℤ) → ZigZag→ℤ (ℤ→ZigZag z) ≡ z
iso-encode-decode (ℤ.pos n) = refl
iso-encode-decode (ℤ.negsuc n) = refl

iso-decode-encode : ∀ (z : ZigZag) → ℤ→ZigZag (ZigZag→ℤ z) ≡ z
iso-decode-encode (zig x) = refl
iso-decode-encode (zag x) = refl

toNat : ZigZag → ℕ
toNat (zig x) = 2 * x
toNat (zag x) = suc (2 * x)

fromNat : ℕ → ZigZag
fromNat zero = zig zero
fromNat (suc zero) = zag zero
fromNat (suc (suc n)) with fromNat n
... | zig x = zig (suc  x)
... | zag x = zag (suc x)



encodeVarint : List Chunk → List Byte
encodeVarint [] = []
encodeVarint (chunk ∷ []) =  (chunk ∷ʳ false)  ∷ [] -- MSB is 0: stop reading
encodeVarint (chunk ∷ rest) = (chunk ∷ʳ true) ∷ encodeVarint rest -- MSB is 1: keep reading

decodeVarint : List Byte → List Chunk
decodeVarint [] = []
decodeVarint ((false ∷ payload) ∷ bytes) = payload ∷ [] -- No more bytes follow
decodeVarint ((true ∷ payload) ∷ bytes) = payload ∷ decodeVarint bytes -- more bytes to follow

-- Takes exactly 'n' bits. Returns the vector and the remaining list.
takePad : ∀ {n : ℕ} → List Bit → Vec Bit n × List Bit
takePad {zero} bs = [] , bs
takePad {suc n} [] = replicate (suc n) false , []
takePad {suc n} (b ∷ bs) =
   let (v , rest) = takePad {n} bs
   in b Vec.∷ v , rest

chunkifyFuel : ℕ → List Bit → List Chunk
chunkifyFuel zero _ = []
chunkifyFuel (suc n) [] = []
chunkifyFuel (suc n) bs =
      let (chunk , rest) = takePad {7} bs
      in chunk ∷ chunkifyFuel n rest

chunkify : List Bit → List Chunk
chunkify [] =  replicate 7 false  ∷ []
chunkify bits =  chunkifyFuel (length bits) bits

incBits : List Bit → List Bit
incBits [] =  true ∷ []
incBits (false ∷ bits) = true ∷ bits
incBits (true ∷ bits) = false ∷ (incBits bits)

toBits : ℕ → List Bit
toBits zero =  []
toBits (suc n) = incBits (toBits n)


fromBits : List Bit → ℕ
fromBits [] = zero
fromBits (false ∷ bits) = 2 * fromBits bits
fromBits (true ∷ bits) = suc (2 * fromBits bits)

fromb-inc≡suc-fromb : ∀ {bits } → fromBits (incBits bits) ≡ suc (fromBits bits)
fromb-inc≡suc-fromb {[]} = refl
fromb-inc≡suc-fromb {false ∷ bits} = refl
fromb-inc≡suc-fromb {true ∷ bits}
            rewrite +-identityʳ (fromBits bits)
                  | +-identityʳ (fromBits (incBits bits))
                  | fromb-inc≡suc-fromb {bits}
                  | +-suc (fromBits bits) (fromBits bits) = refl

fromBits-toBits-n : ∀ (n : ℕ) → fromBits (toBits n) ≡ n
fromBits-toBits-n zero = refl
fromBits-toBits-n(suc n)        = begin
  fromBits (incBits (toBits n)) ≡⟨ fromb-inc≡suc-fromb {toBits n} ⟩
  suc (fromBits (toBits n))     ≡⟨ cong suc (fromBits-toBits-n n) ⟩
  suc n                         ∎

showBit : Bit → String
showBit false = "0"
showBit true = "1"

showBits : List Bit → String
showBits bits = concatStr (mapList showBit bits)


showByte :  Byte → String
showByte bs = showBits (reverse (toList bs))

showBytes : List Byte → String
showBytes [] = ""
showBytes (b ∷ bs) =  (showByte b) <+> showBytes bs

showVarint : ℕ → String
showVarint n = showBytes (encodeVarint (chunkify (toBits n)))

showBinary : ℕ → String
showBinary n = showBits (reverse (toBits n))

_ : showBinary 100 ≡ "1100100"
_ = refl

_ : showVarint 100 ≡ "01100100"
_ = refl

_ : showBinary 178 ≡ "10110010"
_ = refl

_ : showVarint 178 ≡  "10110010 00000001"
_ = refl

_ : showBinary 18000 ≡  "100011001010000"
_ = refl

_ : showVarint 18000 ≡ "11010000 10001100 00000001"
_ = refl

_ : showVarint 200 ≡  "11001000 00000001"
_ = refl

_ : showBinary 200 ≡ "11001000"
_ = refl

_ : showVarint 400 ≡ "10010000 00000011"
_ = refl

_ : showBinary 400 ≡ "110010000"
_ = refl

_ : showVarint 729 ≡  "11011001 00000101"
_ = refl

_ : showBinary 729 ≡ "1011011001"
_ = refl

_ : showVarint 227 ≡  "11100011 00000001"
_ = refl

_ : showBinary 227 ≡ "11100011"
_ = refl



_ : showVarint (toNat (ℤ→ZigZag (ℤ.pos 200))) ≡ "10010000 00000011"
_ = refl


_ : toNat (ℤ→ZigZag (ℤ.negsuc 199)) ≡ 399
_ = refl

_ : showVarint (toNat (ℤ→ZigZag (ℤ.negsuc 199))) ≡ "10001111 00000011"
_ = refl

_ : showBinary 399 ≡ "110001111"
_ = refl

