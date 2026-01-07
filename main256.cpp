#include <bitset>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>

#include "uint256.hpp"

namespace {

using u256::uint256;

struct ios_flags_guard {
   std::ios& os;
   std::ios::fmtflags flags;
   char fill;
   std::streamsize precision;

   explicit ios_flags_guard(std::ios& s)
       : os(s)
       , flags(s.flags())
       , fill(s.fill())
       , precision(s.precision()) {}

   ~ios_flags_guard() {
      os.flags(flags);
      os.fill(fill);
      os.precision(precision);
   }
};

void print_limbs_be(const uint256& v, const char* label) {
   ios_flags_guard g(std::cout);
   std::cout << label << " limbs [w3 w2 w1 w0]: [";
   std::cout << std::hex << std::showbase << v.data()[3] << " " << v.data()[2]
             << " " << v.data()[1] << " " << v.data()[0] << "]\n";
}

void print_bytes(const std::uint8_t b[32], const char* label) {
   ios_flags_guard g(std::cout);
   std::cout << label << " bytes: ";
   std::cout << std::hex << std::setfill('0');
   for (int i = 0; i < 32; ++i) {
      std::cout << std::setw(2) << static_cast<unsigned>(b[i]);
      if (i == 15) std::cout << "  ";
   }
   std::cout << std::dec << "\n";
}

// Build a std::bitset<256> from the underlying 4x64-bit limbs (little-endian).
std::bitset<256> to_bitset(const uint256& x) {
   std::bitset<256> bs;
   const auto* p = x.data();
   for (std::size_t limb = 0; limb < uint256::size(); ++limb) {
      std::uint64_t v = p[limb];
      for (int b = 0; b < 64; ++b) {
         const std::size_t idx = limb * 64u + static_cast<std::size_t>(b);
         bs.set(idx, (v >> b) & 1u);
      }
   }
   return bs;
}

uint256 pow2(unsigned k) {
   uint256 x{1};
   x <<= k;
   return x;
}

void print_banner(const char* title) {
   std::cout << "\n=== " << title << " ===\n";
}

void test_basic() {
   print_banner("basic / bool / comparisons");

   const uint256 z{0};
   const uint256 one{1};
   const uint256 two{2};

   assert(z.is_zero());
   assert(!static_cast<bool>(z));
   assert(static_cast<bool>(one));
   assert(!z);
   assert(!(!one));

   assert(z == uint256{0});
   assert(one != two);
   assert(one < two);
   assert(two > one);
   assert(one <= one);
   assert(two >= one);

   std::cout << "ok\n";
}

void test_add_sub_inc_dec() {
   print_banner("add/sub/inc/dec");

   uint256 a{0};
   ++a;
   assert(a == uint256{1});
   a++;
   assert(a == uint256{2});
   --a;
   assert(a == uint256{1});
   a--;
   assert(a == uint256{0});

   // carry across limbs: (2^64 - 1) + 1 = 2^64
   uint256 x{};
   x.data()[0] = ~std::uint64_t{0};
   x += uint256{1};
   assert(x.data()[0] == 0);
   assert(x.data()[1] == 1);

   // borrow across limbs: 2^64 - 1
   x -= uint256{1};
   assert(x.data()[0] == ~std::uint64_t{0});
   assert(x.data()[1] == 0);

   // modulo wrap: 0 - 1 == 2^256 - 1
   uint256 w{0};
   w -= uint256{1};
   for (std::size_t i = 0; i < uint256::size(); ++i) {
      assert(w.data()[i] == ~std::uint64_t{0});
   }

   std::cout << "ok\n";
}

void test_bitwise_and_shifts() {
   print_banner("bitwise / shifts");

   uint256 a{};
   a.data()[0] = 0x0123456789abcdefULL;
   a.data()[1] = 0xfedcba9876543210ULL;

   uint256 b{};
   b.data()[0] = 0xffff0000ffff0000ULL;
   b.data()[1] = 0x0000ffff0000ffffULL;

   const uint256 andv = a & b;
   const uint256 orv = a | b;
   const uint256 xrv = a ^ b;
   const uint256 notv = ~a;

   assert((andv | xrv) == orv);
   assert((a ^ a).is_zero());
   assert((~notv) == a);

   // shifting 1 by various amounts
   for (unsigned k : {0u, 1u, 63u, 64u, 65u, 127u, 128u, 255u}) {
      const uint256 p = pow2(k);
      uint256 q = p;
      q >>= k;
      assert(q == uint256{1});
   }

   // cross-limb shift check
   uint256 s{1};
   s <<= 64;
   assert(s.data()[0] == 0);
   assert(s.data()[1] == 1);

   s >>= 1;
   assert(s.data()[0] == (1ULL << 63));
   assert(s.data()[1] == 0);

   std::cout << "ok\n";
}

void test_mul() {
   print_banner("multiplication");

   const uint256 a = pow2(200) + uint256{12345};
   const uint256 b = pow2(120) + uint256{67890};
   const uint256 c = a * b;

   // sanity: c / a == b when exact? Not exact due to low-term mixing, so test
   // via distributive pieces:
   const uint256 a0{12345};
   const uint256 a1 = pow2(200);
   const uint256 b0{67890};
   const uint256 b1 = pow2(120);

   const uint256 expected = (a1 * b1) + (a1 * b0) + (a0 * b1) + (a0 * b0);
   assert(c == expected);

   // modulo behavior: (2^255 * 2) wraps to 0 (since 2^256 == 0 mod 2^256)
   const uint256 m = pow2(255);
   assert((m * uint256{2}).is_zero());

   std::cout << "ok\n";
}

void test_div_mod_small() {
   print_banner("division/modulo");

   // exact division
   const uint256 n = pow2(200) + pow2(123) + uint256{999};
   const uint256 d{7};
   const uint256 q = n / d;
   const uint256 r = n % d;
   assert(n == q * d + r);
   assert(r < d);

   // divide by 1
   assert((n / uint256{1}) == n);
   assert((n % uint256{1}).is_zero());

   // n < d
   const uint256 small{5};
   const uint256 big{9};
   assert((small / big).is_zero());
   assert((small % big) == small);

   std::cout << "ok\n";
}

void test_stream_io() {
   print_banner("stream I/O");

   // Compose a value with all limbs touched.
   uint256 x{};
   x.data()[0] = 0x0123456789abcdefULL;
   x.data()[1] = 0xfedcba9876543210ULL;
   x.data()[2] = 0x0f0e0d0c0b0a0908ULL;
   x.data()[3] = 0x8070605040302010ULL;

   // hex output (showbase + uppercase)
   {
      std::ostringstream oss;
      oss << std::showbase << std::uppercase << std::hex << x;
      const std::string s = oss.str();
      assert(s.size() >= 3);
      assert(s[0] == '0' && (s[1] == 'X'));
   }

   // round-trip via hex input
   {
      std::ostringstream oss;
      oss << std::hex << x;
      const std::string hexs = oss.str();

      std::istringstream iss(hexs);
      iss >> std::hex;

      uint256 y{};
      iss >> y;
      assert(iss);
      assert(y == x);
   }

   // decimal output then input (base 10)
   {
      std::ostringstream oss;
      oss << std::dec << x;
      const std::string decs = oss.str();

      std::istringstream iss(decs);
      uint256 y{};
      iss >> y;
      assert(iss);
      assert(y == x);
   }

   // oct output then input (base 8)
   {
      std::ostringstream oss;
      oss << std::oct << x;
      const std::string octs = oss.str();

      std::istringstream iss(octs);
      iss >> std::oct;

      uint256 y{};
      iss >> y;
      assert(iss);
      assert(y == x);
   }

   std::cout << "ok\n";
}

void test_literal_and_bitset() {
   print_banner("literal + bitset interop");

   using namespace u256::literals;

   const uint256 a = "0x1"_u256;
   const uint256 b = "123456789"_u256;
   assert(a == uint256{1});
   assert(b == uint256{123456789});

   const uint256 x = (pow2(255) + uint256{1});
   const auto bs = to_bitset(x);
   assert(bs.test(0));
   assert(bs.test(255));
   assert(bs.count() == 2);

   std::cout << "ok\n";
}

// ---- randomized/property tests ----

struct splitmix64 {
   std::uint64_t s;

   explicit splitmix64(std::uint64_t seed)
       : s(seed) {}

   std::uint64_t next_u64() {
      std::uint64_t z = (s += 0x9e3779b97f4a7c15ULL);
      z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
      z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
      return z ^ (z >> 31);
   }

   unsigned next_u32() { return static_cast<unsigned>(next_u64()); }
};

uint256 random_u256(splitmix64& rng) {
   uint256 x{};
   auto* p = x.data();
   for (std::size_t i = 0; i < uint256::size(); ++i) p[i] = rng.next_u64();
   return x;
}

uint256 random_nonzero_u256(splitmix64& rng) {
   for (;;) {
      uint256 x = random_u256(rng);
      if (x) return x;
   }
}

uint256 random_small_u256(splitmix64& rng) {
   const unsigned bits = rng.next_u32() % 128;
   uint256 x = random_u256(rng);
   if (bits < 256) x >>= (256 - bits);
   return x;
}

void test_properties_random() {
   print_banner("randomized properties");

   splitmix64 rng{0x123456789abcdef0ULL};

   constexpr int N = 2000;
   for (int i = 0; i < N; ++i) {
      const uint256 a = random_u256(rng);
      const uint256 b = random_u256(rng);
      const uint256 c = random_u256(rng);

      assert(a + b == b + a);
      assert((a + b) + c == a + (b + c));

      assert((a ^ a).is_zero());
      assert((a ^ b) ^ b == a);

      assert(~(a & b) == (~a | ~b));
      assert(~(a | b) == (~a & ~b));

      assert(a * (b + c) == (a * b) + (a * c));

      const unsigned k = rng.next_u32() % 256;
      const uint256 p = pow2(k);
      uint256 t = p;
      t >>= k;
      assert(t == uint256{1});
   }

   for (int i = 0; i < 400; ++i) {
      const uint256 n = random_small_u256(rng);
      const uint256 d = random_nonzero_u256(rng);

      const uint256 q = n / d;
      const uint256 r = n % d;

      assert(n == q * d + r);
      assert(r < d);
   }

   std::cout << "ok\n";
}

void test_vs_u64_random() {
   print_banner("randomized cross-check vs uint64_t (low limb)");

   splitmix64 rng{0x0fedcba987654321ULL};

   constexpr int N = 5000;
   for (int i = 0; i < N; ++i) {
      const std::uint64_t a64 = rng.next_u64();
      const std::uint64_t b64 = rng.next_u64();
      const std::uint64_t c64 = (rng.next_u64() | 1ULL);

      const uint256 a{a64};
      const uint256 b{b64};
      const uint256 c{c64};

      {
         const uint256 s = a + b;
         assert(s.data()[0] == static_cast<std::uint64_t>(a64 + b64));

         const std::uint64_t carry =
             (a64 > (std::numeric_limits<std::uint64_t>::max() - b64)) ? 1ULL
                                                                       : 0ULL;
         assert(s.data()[1] == carry);
         assert(s.data()[2] == 0);
         assert(s.data()[3] == 0);
      }
      {
         const uint256 d = a - b;
         assert(d.data()[0] == static_cast<std::uint64_t>(a64 - b64));
      }
      {
         const uint256 m = a * b;
         const unsigned __int128 prod = static_cast<unsigned __int128>(a64) *
                                        static_cast<unsigned __int128>(b64);
         assert(m.data()[0] == static_cast<std::uint64_t>(prod));
         assert(m.data()[1] == static_cast<std::uint64_t>(prod >> 64));
         assert(m.data()[2] == 0);
         assert(m.data()[3] == 0);
      }
      {
         const uint256 q = a / c;
         const uint256 r = a % c;
         assert(q.data()[1] == 0 && q.data()[2] == 0 && q.data()[3] == 0);
         assert(r.data()[0] == static_cast<std::uint64_t>(a64 % c64));
         assert((q * c + r) == a);
      }
      {
         const unsigned sh = static_cast<unsigned>(rng.next_u32() % 64);
         const uint256 sl = a << sh;
         assert(sl.data()[0] == static_cast<std::uint64_t>(a64 << sh));
         const uint256 sr = a >> sh;
         assert(sr.data()[0] == static_cast<std::uint64_t>(a64 >> sh));
      }
   }

   std::cout << "ok\n";
}

// ---- demo ----
void show_value(const char* name, const uint256& v) {
   ios_flags_guard g(std::cout);
   std::cout << name << " (hex): " << std::showbase << std::hex << v << "\n";
   std::cout << name << " (dec): " << std::dec << v << "\n";
}

void demo() {
   print_banner("demo (showcase + interop)");

   using namespace u256::literals;

   const uint256 x =
       "0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"_u256;
   const uint256 y = pow2(200) + uint256{42};

   // Show human-facing forms (MSB on the left).
   show_value("x", x);
   show_value("y", y);

   const uint256 z = x + y;
   show_value("z = x + y", z);

   // ---- Representation demo: limbs vs bytes vs hex ----
   std::cout << "\nrepresentation demo (note: printing is big-endian)\n";
   print_limbs_be(x, "x");

   std::uint8_t be[32]{};
   std::uint8_t le[32]{};
   x.to_bytes_be(be);
   x.to_bytes_le(le);

   print_bytes(be, "x (big-endian)");
   print_bytes(le, "x (little-endian)");

   // Round-trip bytes
   const uint256 xb = uint256::from_bytes_be(be);
   const uint256 xl = uint256::from_bytes_le(le);
   assert(xb == x);
   assert(xl == x);

   // Hex string interop (big-endian string)
   const std::string hx = x.to_hex_be(/*prefix=*/true, /*uppercase=*/false);
   std::cout << "x.to_hex_be(): " << hx << "\n";

   bool ok = false;
   const uint256 xp = uint256::from_hex_be(hx, ok);
   assert(ok);
   assert(xp == x);

   // Demonstrate that underscores are accepted (if you enabled it)
   {
      std::string hx2 = hx;
      // insert a couple underscores in safe places
      if (hx2.size() > 10) hx2.insert(10, "_");
      if (hx2.size() > 30) hx2.insert(30, "_");
      bool ok2 = false;
      const uint256 xu = uint256::from_hex_be(hx2, ok2);
      assert(ok2);
      assert(xu == x);
      std::cout << "from_hex_be() accepts '_' separators: ok\n";
   }

   // ---- Bitcoin-style “hash” display example ----
   // A typical block hash is shown as 32 bytes, big-endian hex.
   const std::string hash_hex =
       "00000000000000000000144d46277fbe49c3216eeea45e85408b3465b88978d5";
   assert(hash_hex.size() == 64); // demo invariant: “this is a 32-byte hash”

   bool okh = false;
   const uint256 h = uint256::from_hex_be(hash_hex, okh);
   assert(okh);

   std::uint8_t hbe[32]{};
   h.to_bytes_be(hbe);

   std::cout << "\nbitcoin-style hash example\n";
   std::cout << "hash input:  " << hash_hex << "\n";
   std::cout << "hash parsed: " << h.to_hex_be(false, false) << "\n";
   print_bytes(hbe, "hash (big-endian)");
   assert(h.to_hex_be_fixed(false, false) == hash_hex); // exact round-trip
   {
      bool oks = false;
      const uint256 s = uint256::from_hex_be("1", oks);
      assert(oks);
      assert(s == uint256{1});
      std::cout << "short hex \"1\" parses as: " << std::showbase << std::hex
                << s << std::dec << "\n";
   }

   // ---- bitwise / shift / div demo (as before, but kept short) ----
   {
      // Carry across 64-bit boundary: (2^64 - 1) + 1 = 2^64
      uint256 a{};
      a.data()[0] = ~std::uint64_t{0};
      const uint256 b{1};
      const uint256 c = a + b;

      ios_flags_guard g(std::cout);
      std::cout << "\ncarry demo:\n";
      std::cout << "  a = " << std::showbase << std::hex << a << "\n";
      std::cout << "  b = " << std::showbase << std::hex << b << "\n";
      std::cout << "  c = a + b = " << std::showbase << std::hex << c << "\n";
      std::cout << "  c limbs: [" << std::hex << c.data()[3] << " "
                << c.data()[2] << " " << c.data()[1] << " " << c.data()[0]
                << "]\n";
   }

   {
      ios_flags_guard g(std::cout);
      std::cout << "\nshift boundaries:\n";
      for (unsigned k : {63u, 64u, 65u, 127u, 128u, 129u}) {
         uint256 t{1};
         t <<= k;
         std::cout << "  1<<" << std::dec << k << " = " << std::showbase
                   << std::hex << t << "\n";
      }
   }

   {
      const uint256 n = x;
      const uint256 d{97};
      const uint256 q = n / d;
      const uint256 r = n % d;

      ios_flags_guard g(std::cout);
      std::cout << "\ndiv/mod demo:\n";
      std::cout << "  n = " << std::showbase << std::hex << n << "\n";
      std::cout << "  d = " << std::dec << 97 << "\n";
      std::cout << "  q = n / d = " << std::showbase << std::hex << q << "\n";
      std::cout << "  r = n % d = " << std::dec << r << "\n";
      assert(n == q * d + r);
   }

   {
      const auto bs = to_bitset(y);
      std::cout << "\nbitset demo:\n";
      std::cout << "  y popcount: " << bs.count() << "\n";
      std::cout << "  y bit 200:  " << bs.test(200) << "\n";
      std::cout << "  y bit 0:    " << bs.test(0) << "\n";
   }
}

template<class F>
std::uint64_t time_it_us(F&& f) {
   using clock = std::chrono::steady_clock;
   const auto t0 = clock::now();
   f();
   const auto t1 = clock::now();
   return static_cast<std::uint64_t>(
       std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count());
}

void micro_bench() {
   print_banner("micro-bench (rough)");

   // Keep it deterministic.
   splitmix64 rng{0xdeadbeefcafebabeULL};

   constexpr int N = 20000;
   uint256 acc{0};
   uint256 a = random_u256(rng);
   uint256 b = random_u256(rng);
   uint256 c = random_nonzero_u256(rng);

   const auto add_us = time_it_us([&] {
      for (int i = 0; i < N; ++i) {
         a = a + b;
         acc ^= a;
         b = random_u256(rng);
      }
   });

   const auto mul_us = time_it_us([&] {
      for (int i = 0; i < N; ++i) {
         a = a * b;
         acc ^= a;
         b = random_u256(rng);
      }
   });

   // Division is expensive; use fewer iterations.
   constexpr int Nd = 2000;
   const auto div_us = time_it_us([&] {
      for (int i = 0; i < Nd; ++i) {
         a = a / c;
         acc ^= a;
         c = random_nonzero_u256(rng);
      }
   });

   // Prevent “optimized away”.
   if (!acc.is_zero()) {
      // do nothing
   }

   std::cout << "  add/xor  : " << add_us << " us for " << N << " iterations\n";
   std::cout << "  mul/xor  : " << mul_us << " us for " << N << " iterations\n";
   std::cout << "  div/xor  : " << div_us << " us for " << Nd
             << " iterations\n";
}

} // namespace

int main() {
   test_basic();
   test_add_sub_inc_dec();
   test_bitwise_and_shifts();
   test_mul();
   test_div_mod_small();
   test_stream_io();
   test_literal_and_bitset();

   test_properties_random();
   test_vs_u64_random();

   demo();
   micro_bench();

   std::cout << "\nAll tests passed.\n";
}

