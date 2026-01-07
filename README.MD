# WARNING!

This program is for **educational use only** and has not been vetted for correctness,
conformity, or undefined behavior. Do not use this in a production environment.

## Description

This code implements a simple SHA256 hashing utility. Emphasis has been placed on
clarity over performance. Testing is limited to Intel x86 and Apple Silicon on macOS
in the terminal and Linux/Unix systems. While the code is written in pure C++
and should be portable, no such promise is made.

The standard being implemented can be found in [FIPS PUB 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).

## Compilation

To compile the source, simply type the following at the command line prompt:

```
c++ -std=c++20 -O3 -o sha256 sha256.cpp
```
## Copying

This software is placed into the public domain by the author.

# uint256

This is just me playing around with creating my own 256 bit unsigned integer
type. I'm also placing it in the public domain. There are certainly better
implementations such as in Boost::multiprecision. If you wish to play with
it, feel free. I wouldn't use it in production though. The code consists of
a header only implementation and a test `main256.cpp` file.

To compile it, I've been using:

```
c++ --std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -o main256 main256.cpp
```

