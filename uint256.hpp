#pragma once
// uint256.hpp - header-only 256-bit unsigned integer for C++20/23
//
// - Trivially copyable, standard layout
// - No dependencies beyond the standard library
// - Limb layout: little-endian (limb 0 = least significant 64 bits)
// - Stream I/O honors std::ios basefield (dec/hex/oct) and showbase for
// hex/octal
//
// Notes:
// - This implementation relies on unsigned __int128 for fast carry/borrow and
// division by uint64.
//   Clang/GCC support it. If you need MSVC, add a _umul128/_udiv128 path.

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iomanip>
#include <ios>
#include <istream>
#include <limits>
#include <ostream>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>

#if !defined(__SIZEOF_INT128__)
static_assert(
    false,
    "uint256 requires compiler support for unsigned __int128 (Clang/GCC).");
#endif

namespace u256 {

struct uint256 final {
   using limb_type = std::uint64_t;
   static constexpr int limb_count = 4;
   static constexpr int bit_width = 256;

   limb_type w[limb_count]{}; // little-endian limbs

   // --- trivial construction ---
   constexpr uint256() noexcept = default;
   constexpr uint256(const uint256&) noexcept = default;
   constexpr uint256& operator=(const uint256&) noexcept = default;

   // NOLINTNEXTLINE(google-explicit-constructor)
   constexpr uint256(std::uint64_t x) noexcept { w[0] = x; }

   // Construct from any unsigned integral up to 64 bits.
   template<class UInt>
      requires(std::is_integral_v<UInt> && std::is_unsigned_v<UInt> &&
               (sizeof(UInt) <= sizeof(std::uint64_t)))
   // NOLINTNEXTLINE(google-explicit-constructor)
   constexpr uint256(UInt x) noexcept
       : uint256(static_cast<std::uint64_t>(x)) {}

   // Construct explicitly from signed integrals (mod 2^256, like casting to an
   // unsigned type).
   template<class SInt>
      requires(std::is_integral_v<SInt> && std::is_signed_v<SInt> &&
               (sizeof(SInt) <= sizeof(std::int64_t)))
   explicit constexpr uint256(SInt x) noexcept {
      // Convert through uint64_t so negative values become 2^64 - |x| in the
      // low limb.
      w[0] = static_cast<std::uint64_t>(x);
   }

   // Narrowing conversions (explicit, like good taste).
   explicit constexpr operator std::uint64_t() const noexcept { return w[0]; }

   // Access for easy interop (e.g., std::bitset building elsewhere).
   [[nodiscard]] constexpr limb_type* data() noexcept { return w; }
   [[nodiscard]] constexpr const limb_type* data() const noexcept { return w; }
   [[nodiscard]] static constexpr std::size_t size() noexcept {
      return limb_count;
   }

   // --- basic queries ---
   [[nodiscard]] constexpr bool is_zero() const noexcept {
      return (w[0] | w[1] | w[2] | w[3]) == 0;
   }

   // Like native unsigneds: usable in boolean contexts.
   explicit constexpr operator bool() const noexcept { return !is_zero(); }
   [[nodiscard]] constexpr bool operator!() const noexcept { return is_zero(); }

   // --- comparisons ---
   friend constexpr bool operator==(const uint256& a,
                                    const uint256& b) noexcept {
      return a.w[0] == b.w[0] && a.w[1] == b.w[1] && a.w[2] == b.w[2] &&
             a.w[3] == b.w[3];
   }
   friend constexpr bool operator!=(const uint256& a,
                                    const uint256& b) noexcept {
      return !(a == b);
   }

   friend constexpr bool operator<(const uint256& a,
                                   const uint256& b) noexcept {
      for (int i = limb_count - 1; i >= 0; --i) {
         if (a.w[i] != b.w[i]) return a.w[i] < b.w[i];
      }
      return false;
   }
   friend constexpr bool operator>(const uint256& a,
                                   const uint256& b) noexcept {
      return b < a;
   }
   friend constexpr bool operator<=(const uint256& a,
                                    const uint256& b) noexcept {
      return !(b < a);
   }
   friend constexpr bool operator>=(const uint256& a,
                                    const uint256& b) noexcept {
      return !(a < b);
   }

   // --- bitwise ---
   friend constexpr uint256 operator~(uint256 x) noexcept {
      x.w[0] = ~x.w[0];
      x.w[1] = ~x.w[1];
      x.w[2] = ~x.w[2];
      x.w[3] = ~x.w[3];
      return x;
   }

   friend constexpr uint256 operator&(uint256 a, const uint256& b) noexcept {
      a.w[0] &= b.w[0];
      a.w[1] &= b.w[1];
      a.w[2] &= b.w[2];
      a.w[3] &= b.w[3];
      return a;
   }
   friend constexpr uint256 operator|(uint256 a, const uint256& b) noexcept {
      a.w[0] |= b.w[0];
      a.w[1] |= b.w[1];
      a.w[2] |= b.w[2];
      a.w[3] |= b.w[3];
      return a;
   }
   friend constexpr uint256 operator^(uint256 a, const uint256& b) noexcept {
      a.w[0] ^= b.w[0];
      a.w[1] ^= b.w[1];
      a.w[2] ^= b.w[2];
      a.w[3] ^= b.w[3];
      return a;
   }

   constexpr uint256& operator&=(const uint256& b) noexcept {
      return *this = (*this & b);
   }
   constexpr uint256& operator|=(const uint256& b) noexcept {
      return *this = (*this | b);
   }
   constexpr uint256& operator^=(const uint256& b) noexcept {
      return *this = (*this ^ b);
   }

   // --- shifts ---
   friend constexpr uint256 operator<<(uint256 a, unsigned s) noexcept {
      a <<= s;
      return a;
   }
   friend constexpr uint256 operator>>(uint256 a, unsigned s) noexcept {
      a >>= s;
      return a;
   }

   constexpr uint256& operator<<=(unsigned s) noexcept {
      if (s >= bit_width) {
         *this = uint256{};
         return *this;
      }
      const unsigned limb_shift = s / 64;
      const unsigned bit_shift = s % 64;

      if (limb_shift != 0) {
         for (int i = limb_count - 1; i >= 0; --i) {
            w[i] = (i >= static_cast<int>(limb_shift)) ? w[i - limb_shift] : 0;
         }
      }
      if (bit_shift != 0) {
         for (int i = limb_count - 1; i >= 0; --i) {
            const limb_type hi = w[i] << bit_shift;
            const limb_type carry =
                (i > 0) ? (w[i - 1] >> (64 - bit_shift)) : 0;
            w[i] = hi | carry;
         }
      }
      return *this;
   }

   constexpr uint256& operator>>=(unsigned s) noexcept {
      if (s >= bit_width) {
         *this = uint256{};
         return *this;
      }
      const unsigned limb_shift = s / 64;
      const unsigned bit_shift = s % 64;

      if (limb_shift != 0) {
         for (int i = 0; i < limb_count; ++i) {
            w[i] = (i + limb_shift < static_cast<unsigned>(limb_count))
                       ? w[i + limb_shift]
                       : 0;
         }
      }
      if (bit_shift != 0) {
         for (int i = 0; i < limb_count; ++i) {
            const limb_type lo = w[i] >> bit_shift;
            const limb_type carry =
                (i + 1 < limb_count) ? (w[i + 1] << (64 - bit_shift)) : 0;
            w[i] = lo | carry;
         }
      }
      return *this;
   }

   // --- byte interop (32 bytes) ---
   constexpr void to_bytes_le(std::uint8_t out[32]) const noexcept {
      for (int i = 0; i < limb_count; ++i) {
         const std::uint64_t v = w[i];
         out[i * 8 + 0] = static_cast<std::uint8_t>(v >> 0);
         out[i * 8 + 1] = static_cast<std::uint8_t>(v >> 8);
         out[i * 8 + 2] = static_cast<std::uint8_t>(v >> 16);
         out[i * 8 + 3] = static_cast<std::uint8_t>(v >> 24);
         out[i * 8 + 4] = static_cast<std::uint8_t>(v >> 32);
         out[i * 8 + 5] = static_cast<std::uint8_t>(v >> 40);
         out[i * 8 + 6] = static_cast<std::uint8_t>(v >> 48);
         out[i * 8 + 7] = static_cast<std::uint8_t>(v >> 56);
      }
   }

   constexpr void to_bytes_be(std::uint8_t out[32]) const noexcept {
      for (int i = 0; i < limb_count; ++i) {
         const std::uint64_t v = w[limb_count - 1 - i];
         out[i * 8 + 0] = static_cast<std::uint8_t>(v >> 56);
         out[i * 8 + 1] = static_cast<std::uint8_t>(v >> 48);
         out[i * 8 + 2] = static_cast<std::uint8_t>(v >> 40);
         out[i * 8 + 3] = static_cast<std::uint8_t>(v >> 32);
         out[i * 8 + 4] = static_cast<std::uint8_t>(v >> 24);
         out[i * 8 + 5] = static_cast<std::uint8_t>(v >> 16);
         out[i * 8 + 6] = static_cast<std::uint8_t>(v >> 8);
         out[i * 8 + 7] = static_cast<std::uint8_t>(v >> 0);
      }
   }

   static constexpr uint256 from_bytes_le(const std::uint8_t in[32]) noexcept {
      uint256 x{};
      for (int i = 0; i < limb_count; ++i) {
         x.w[i] = (static_cast<std::uint64_t>(in[i * 8 + 0]) << 0) |
                  (static_cast<std::uint64_t>(in[i * 8 + 1]) << 8) |
                  (static_cast<std::uint64_t>(in[i * 8 + 2]) << 16) |
                  (static_cast<std::uint64_t>(in[i * 8 + 3]) << 24) |
                  (static_cast<std::uint64_t>(in[i * 8 + 4]) << 32) |
                  (static_cast<std::uint64_t>(in[i * 8 + 5]) << 40) |
                  (static_cast<std::uint64_t>(in[i * 8 + 6]) << 48) |
                  (static_cast<std::uint64_t>(in[i * 8 + 7]) << 56);
      }
      return x;
   }

   static constexpr uint256 from_bytes_be(const std::uint8_t in[32]) noexcept {
      uint256 x{};
      for (int i = 0; i < limb_count; ++i) {
         const int o = i * 8;
         const std::uint64_t v = (static_cast<std::uint64_t>(in[o + 0]) << 56) |
                                 (static_cast<std::uint64_t>(in[o + 1]) << 48) |
                                 (static_cast<std::uint64_t>(in[o + 2]) << 40) |
                                 (static_cast<std::uint64_t>(in[o + 3]) << 32) |
                                 (static_cast<std::uint64_t>(in[o + 4]) << 24) |
                                 (static_cast<std::uint64_t>(in[o + 5]) << 16) |
                                 (static_cast<std::uint64_t>(in[o + 6]) << 8) |
                                 (static_cast<std::uint64_t>(in[o + 7]) << 0);
         x.w[limb_count - 1 - i] = v;
      }
      return x;
   }

   // --- hex string interop (big-endian, common display form) ---
   [[nodiscard]] std::string to_hex_be(bool prefix = false,
                                       bool uppercase = false) const {
      static constexpr char lo[] = "0123456789abcdef";
      static constexpr char up[] = "0123456789ABCDEF";
      const char* digits = uppercase ? up : lo;

      std::uint8_t bytes[32];
      to_bytes_be(bytes);

      std::string s;
      s.reserve((prefix ? 2 : 0) + 64);
      if (prefix) s += (uppercase ? "0X" : "0x");

      bool started = false;
      for (int i = 0; i < 32; ++i) {
         const std::uint8_t b = bytes[i];
         const char hi = digits[(b >> 4) & 0xF];
         const char loch = digits[b & 0xF];

         if (!started) {
            if (hi != '0' || loch != '0' || i == 31)
               started = true;
            else
               continue;
         }
         if (!started) continue;

         // If we "started" on a byte boundary, we still want both nibbles.
         s.push_back(hi);
         s.push_back(loch);
      }

      // If we skipped leading zero bytes, we might have skipped everything
      // except last byte case; ensure non-empty.
      if (s.empty() || (prefix && s.size() == 2)) s += '0';
      return s;
   }

   [[nodiscard]] std::string to_hex_be_fixed(bool prefix = false,
                                             bool uppercase = false) const {
      static constexpr char lo[] = "0123456789abcdef";
      static constexpr char up[] = "0123456789ABCDEF";
      const char* digits = uppercase ? up : lo;

      std::uint8_t bytes[32];
      to_bytes_be(bytes);

      std::string s;
      s.reserve((prefix ? 2 : 0) + 64);
      if (prefix) s += (uppercase ? "0X" : "0x");

      for (int i = 0; i < 32; ++i) {
         const std::uint8_t b = bytes[i];
         s.push_back(digits[(b >> 4) & 0xF]);
         s.push_back(digits[b & 0xF]);
      }
      return s;
   }

   static uint256 from_hex_be(std::string_view sv, bool& ok) noexcept {
      ok = false;

      if (sv.size() >= 2 && sv[0] == '0' && (sv[1] == 'x' || sv[1] == 'X'))
         sv.remove_prefix(2);

      // allow underscores
      std::string compact;
      compact.reserve(sv.size());
      for (char c : sv) {
         if (c != '_') compact.push_back(c);
      }

      if (compact.empty()) return uint256{};
      if (compact.size() > 64) return uint256{};

      // If odd length, pretend there's a leading '0'.
      const bool odd = (compact.size() % 2) != 0;

      std::uint8_t bytes[32]{};
      std::size_t bi = 32; // fill from the end (least significant byte)
      std::size_t i = compact.size();

      auto hex_val = [](char c) constexpr noexcept -> int {
         if (c >= '0' && c <= '9') return c - '0';
         if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
         if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
         return -1;
      };

      while (i > 0) {
         int lo_n = hex_val(compact[i - 1]);
         if (lo_n < 0) return uint256{};
         int hi_n = 0;

         if (i >= 2) {
            hi_n = hex_val(compact[i - 2]);
            if (hi_n < 0) return uint256{};
            i -= 2;
         } else {
            // only one nibble left
            if (!odd) return uint256{};
            hi_n = 0;
            i -= 1;
         }

         if (bi == 0) return uint256{};
         bytes[--bi] = static_cast<std::uint8_t>((hi_n << 4) | lo_n);
      }

      ok = true;
      return from_bytes_be(bytes);
   }

   // --- arithmetic helpers ---
 private:
   static constexpr limb_type add_carry(limb_type a, limb_type b,
                                        limb_type& carry) noexcept {
      const unsigned __int128 sum = static_cast<unsigned __int128>(a) +
                                    static_cast<unsigned __int128>(b) +
                                    static_cast<unsigned __int128>(carry);
      carry = static_cast<limb_type>(sum >> 64);
      return static_cast<limb_type>(sum);
   }

   static constexpr limb_type sub_borrow(limb_type a, limb_type b,
                                         limb_type& borrow) noexcept {
      const unsigned __int128 aa = static_cast<unsigned __int128>(a);
      const unsigned __int128 bb = static_cast<unsigned __int128>(b) +
                                   static_cast<unsigned __int128>(borrow);
      const unsigned __int128 diff = aa - bb;
      // If aa < bb, the top bit of the 128-bit result will be 1 due to
      // underflow in unsigned arithmetic.
      borrow = (aa < bb) ? 1u : 0u;
      return static_cast<limb_type>(diff);
   }

   [[nodiscard]] constexpr bool get_bit(unsigned i) const noexcept {
      const unsigned li = i / 64;
      const unsigned bi = i % 64;
      return (w[li] >> bi) & 1u;
   }

   constexpr void set_bit(unsigned i) noexcept {
      const unsigned li = i / 64;
      const unsigned bi = i % 64;
      w[li] |= (limb_type{1} << bi);
   }

   static constexpr uint256 shl1(uint256 x) noexcept {
      limb_type carry = 0;
      for (int i = 0; i < limb_count; ++i) {
         const limb_type next = x.w[i] >> 63;
         x.w[i] = (x.w[i] << 1) | carry;
         carry = next;
      }
      return x;
   }

   // Divide a 256-bit value by a 64-bit divisor. Returns quotient; sets
   // remainder.
   static constexpr uint256 divmod_u64(const uint256& n, limb_type d,
                                       limb_type& rem) noexcept {
      uint256 q{};
      unsigned __int128 r = 0;
      for (int i = limb_count - 1; i >= 0; --i) {
         r = (r << 64) | n.w[i];
         const limb_type qi = static_cast<limb_type>(r / d);
         r = r % d;
         q.w[i] = qi;
      }
      rem = static_cast<limb_type>(r);
      return q;
   }

 public:
   // --- +, - ---
   friend constexpr uint256 operator+(uint256 a, const uint256& b) noexcept {
      limb_type c = 0;
      a.w[0] = add_carry(a.w[0], b.w[0], c);
      a.w[1] = add_carry(a.w[1], b.w[1], c);
      a.w[2] = add_carry(a.w[2], b.w[2], c);
      a.w[3] = add_carry(a.w[3], b.w[3], c);
      return a; // modulo 2^256
   }

   friend constexpr uint256 operator-(uint256 a, const uint256& b) noexcept {
      limb_type br = 0;
      a.w[0] = sub_borrow(a.w[0], b.w[0], br);
      a.w[1] = sub_borrow(a.w[1], b.w[1], br);
      a.w[2] = sub_borrow(a.w[2], b.w[2], br);
      a.w[3] = sub_borrow(a.w[3], b.w[3], br);
      return a; // modulo 2^256
   }

   constexpr uint256& operator+=(const uint256& b) noexcept {
      return *this = (*this + b);
   }
   constexpr uint256& operator-=(const uint256& b) noexcept {
      return *this = (*this - b);
   }

   // --- unary + / - (like native unsigned: unary - is modulo) ---
   friend constexpr uint256 operator+(uint256 x) noexcept { return x; }
   friend constexpr uint256 operator-(uint256 x) noexcept {
      return uint256{} - x;
   }

   // --- increment/decrement ---
   constexpr uint256& operator++() noexcept {
      *this += uint256{1};
      return *this;
   }
   constexpr uint256 operator++(int) noexcept {
      uint256 t = *this;
      ++(*this);
      return t;
   }
   constexpr uint256& operator--() noexcept {
      *this -= uint256{1};
      return *this;
   }
   constexpr uint256 operator--(int) noexcept {
      uint256 t = *this;
      --(*this);
      return t;
   }

   // --- multiplication (mod 2^256) ---
   friend constexpr uint256 operator*(const uint256& a,
                                      const uint256& b) noexcept {
      uint256 r{};
      for (int i = 0; i < limb_count; ++i) {
         unsigned __int128 carry = 0;
         for (int j = 0; j + i < limb_count; ++j) {
            const unsigned __int128 cur =
                static_cast<unsigned __int128>(a.w[i]) *
                    static_cast<unsigned __int128>(b.w[j]) +
                static_cast<unsigned __int128>(r.w[i + j]) + carry;
            r.w[i + j] = static_cast<limb_type>(cur);
            carry = cur >> 64;
         }
         // overflow beyond 256 bits is discarded (native unsigned behavior
         // modulo 2^N)
      }
      return r;
   }

   constexpr uint256& operator*=(const uint256& b) noexcept {
      return *this = (*this * b);
   }

   // --- division/modulo (long division in bits; correct, predictable, not
   // fancy) ---
   friend constexpr uint256 operator/(const uint256& n,
                                      const uint256& d) noexcept {
      uint256 q{}, r{};
      if (d.is_zero()) return q; // like UB in native; choose benign result
      for (int i = bit_width - 1; i >= 0; --i) {
         r = shl1(r);
         if (n.get_bit(static_cast<unsigned>(i))) r.w[0] |= 1u;
         if (r >= d) {
            r -= d;
            q.set_bit(static_cast<unsigned>(i));
         }
      }
      return q;
   }

   friend constexpr uint256 operator%(const uint256& n,
                                      const uint256& d) noexcept {
      uint256 q{}, r{};
      if (d.is_zero()) return r; // benign
      for (int i = bit_width - 1; i >= 0; --i) {
         r = shl1(r);
         if (n.get_bit(static_cast<unsigned>(i))) r.w[0] |= 1u;
         if (r >= d) {
            r -= d;
            q.set_bit(static_cast<unsigned>(i));
         }
      }
      return r;
   }

   constexpr uint256& operator/=(const uint256& d) noexcept {
      return *this = (*this / d);
   }
   constexpr uint256& operator%=(const uint256& d) noexcept {
      return *this = (*this % d);
   }

   // --- stream I/O helpers ---
 private:
   static constexpr int digit_val(char c) noexcept {
      if (c >= '0' && c <= '9') return c - '0';
      if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
      if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
      return -1;
   }

   static uint256 parse_base(std::string_view s, unsigned base,
                             bool& ok) noexcept {
      ok = false;
      uint256 x{};
      if (s.empty()) return x;

      for (char c : s) {
         if (c == '_') continue; // allow digit separators
         const int v = digit_val(c);
         if (v < 0 || static_cast<unsigned>(v) >= base) return uint256{};
         x = x * uint256{base} + uint256{static_cast<std::uint64_t>(v)};
      }
      ok = true;
      return x;
   }

 public:
   // Stream output: honor basefield and showbase; default is decimal.
   friend std::ostream& operator<<(std::ostream& os, const uint256& x) {
      const auto basefield = os.flags() & std::ios::basefield;
      const bool showbase = (os.flags() & std::ios::showbase) != 0;
      const bool upper = (os.flags() & std::ios::uppercase) != 0;

      // --- hex ---
      if (basefield == std::ios::hex) {
         std::string out;
         out.reserve((showbase ? 2 : 0) + 64);

         if (showbase) out += (upper ? "0X" : "0x");

         bool started = false;
         for (int i = limb_count - 1; i >= 0; --i) {
            const auto limb = x.w[i];
            for (int nib = 15; nib >= 0; --nib) {
               const unsigned v =
                   static_cast<unsigned>((limb >> (nib * 4)) & 0xFu);
               if (!started) {
                  if (v == 0 && (i != 0 || nib != 0)) continue;
                  started = true;
               }
               const char d =
                   (v < 10) ? static_cast<char>('0' + v)
                            : static_cast<char>((upper ? 'A' : 'a') + (v - 10));
               out.push_back(d);
            }
         }
         if (!started) out.push_back('0');
         return os << out;
      }

      // --- oct ---
      if (basefield == std::ios::oct) {
         if (x.is_zero()) return os << '0';

         static constexpr std::uint64_t chunk_base = (1ull << 63); // 8^21
         static constexpr int chunk_digits = 21;

         struct chunk {
            std::uint64_t v;
            bool last;
         };
         chunk cs[40];
         int cn = 0;

         uint256 t = x;
         while (!t.is_zero()) {
            std::uint64_t rem = 0;
            t = divmod_u64(t, chunk_base, rem);
            cs[cn++] = chunk{rem, t.is_zero()};
         }

         if (showbase) os << '0';

         for (int k = cn - 1; k >= 0; --k) {
            std::uint64_t rem = cs[k].v;

            char buf[chunk_digits];
            for (int i = 0; i < chunk_digits; ++i) {
               buf[i] = static_cast<char>('0' + (rem & 7u));
               rem >>= 3;
            }

            if (k == cn - 1) {
               // most significant chunk: strip leading zeros
               int i = chunk_digits - 1;
               while (i > 0 && buf[i] == '0') --i;
               for (; i >= 0; --i) os << buf[i];
            } else {
               // lower chunks: fixed width (leading zeros)
               for (int i = chunk_digits - 1; i >= 0; --i) os << buf[i];
            }
         }

         return os;
      }

      // --- dec (default) ---
      if (x.is_zero()) return os << '0';

      static constexpr std::uint64_t base = 10000000000000000000ull; // 1e19
      struct piece {
         std::uint64_t v;
         bool last;
      };
      piece ps[32];
      int pn = 0;

      uint256 t = x;
      while (!t.is_zero()) {
         std::uint64_t rem = 0;
         t = divmod_u64(t, base, rem);
         ps[pn++] = piece{rem, t.is_zero()};
      }

      // print most significant piece without padding, then pad each lower piece
      // to 19 digits
      for (int i = pn - 1; i >= 0; --i) {
         if (i == pn - 1) {
            os << ps[i].v;
         } else {
            const auto old_fill = os.fill('0');
            os << std::setw(19) << ps[i].v;
            os.fill(old_fill);
         }
      }
      return os;
   }

   // Stream input: honors basefield (dec/hex/oct). Accepts optional 0x/0X for
   // hex when basefield is dec, too.
   friend std::istream& operator>>(std::istream& is, uint256& x) {
      std::string s;
      is >> s;
      if (!is) return is;

      // Determine base from flags; also accept 0x prefix when in dec mode
      // (common behavior).
      unsigned base = 10;
      const auto basefield = is.flags() & std::ios::basefield;
      if (basefield == std::ios::hex)
         base = 16;
      else if (basefield == std::ios::oct)
         base = 8;

      std::string_view sv{s};

      if (base == 10 && sv.size() >= 2 && sv[0] == '0' &&
          (sv[1] == 'x' || sv[1] == 'X')) {
         base = 16;
         sv.remove_prefix(2);
      } else if (base == 10 && sv.size() >= 1 && sv[0] == '+') {
         sv.remove_prefix(1);
      }

      if (sv.empty()) {
         is.setstate(std::ios::failbit);
         return is;
      }

      bool ok = false;
      const uint256 parsed = parse_base(sv, base, ok);
      if (!ok) {
         is.setstate(std::ios::failbit);
         return is;
      }
      x = parsed;
      return is;
   }
};

// Ensure “native-like” properties.
static_assert(std::is_trivially_copyable_v<uint256>);
static_assert(std::is_standard_layout_v<uint256>);
static_assert(sizeof(uint256) == 32);

// Optional literal: 0x..._u256 or decimal ..._u256
namespace literals {

constexpr int digit_val_(char c) noexcept {
   if (c >= '0' && c <= '9') return c - '0';
   if (c >= 'a' && c <= 'f') return 10 + (c - 'a');
   if (c >= 'A' && c <= 'F') return 10 + (c - 'A');
   return -1;
}

constexpr u256::uint256 operator"" _u256(unsigned long long v) noexcept {
   return u256::uint256{static_cast<std::uint64_t>(v)};
}

constexpr uint256 operator"" _u256(const char* s, std::size_t n) noexcept {
   std::string_view sv{s, n};
   unsigned base = 10;
   if (sv.size() >= 2 && sv[0] == '0' && (sv[1] == 'x' || sv[1] == 'X')) {
      base = 16;
      sv.remove_prefix(2);
   }

   bool ok = true;
   uint256 v{};
   if (sv.empty()) ok = false;

   for (char c : sv) {
      if (c == '_') continue;
      const int dv = digit_val_(c);
      if (dv < 0 || static_cast<unsigned>(dv) >= base) {
         ok = false;
         break;
      }
      v = v * uint256{base} + uint256{static_cast<std::uint64_t>(dv)};
   }
   return ok ? v : uint256{};
}

} // namespace literals

} // namespace u256

namespace std {

template<>
class numeric_limits<u256::uint256> {
 public:
   static constexpr bool is_specialized = true;

   static constexpr u256::uint256 min() noexcept { return u256::uint256{0}; }

   static constexpr u256::uint256 max() noexcept {
      u256::uint256 x{};
      x.data()[0] = ~std::uint64_t{0};
      x.data()[1] = ~std::uint64_t{0};
      x.data()[2] = ~std::uint64_t{0};
      x.data()[3] = ~std::uint64_t{0};
      return x;
   }

   static constexpr int digits = 256;
   static constexpr int digits10 = 77;

   static constexpr bool is_signed = false;
   static constexpr bool is_integer = true;
   static constexpr bool is_exact = true;

   static constexpr bool is_bounded = true;
   static constexpr bool is_modulo = true;

   static constexpr bool has_infinity = false;
   static constexpr bool has_quiet_NaN = false;
   static constexpr bool has_signaling_NaN = false;

   static constexpr bool traps = false;
};

} // namespace std

