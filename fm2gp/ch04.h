// Copyright (c) 2014 Alexander A. Stepanov and Daniel E. Rose
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.
//
// This code accompanies the "fM2GP" book:
//
//	From Mathematics to Generic Programming
//	by Alexander Stepanov and Daniel E. Rose
//	Addison-Wesley Professional, 2015
//
// -------------------------------------------------------------------
// ch04.h -- Functions from Chapter 4 of fM2GP.
// -------------------------------------------------------------------

#include <algorithm>

using line_segment = unsigned;
using integer = unsigned;

// Section 4.2

bool odd(unsigned n) { return n & 0x1; }
auto half(unsigned n) { return n >> 1; }

auto gcm0(line_segment a, line_segment b) {
    while (a != b) {
        if (b < a) a = a - b;
        else b = b - a;
    }
    return a;
}

auto gcm1(line_segment a, line_segment b) {
    while (a != b) {
        while (b < a) a = a - b;
        std::swap(a, b);
    }
    return a;
}

auto segment_remainder(line_segment a, line_segment b) {
    while (b < a) a = a - b;
    return a;
}

auto gcm(line_segment a, line_segment b) {
    while (a != b) {
        a = segment_remainder(a, b);
        std::swap(a, b);
    }
    return a;
}

auto fast_segment_remainder(line_segment a, line_segment b) {
    if (a <= b) return a;
    if (a - b <= b) return a - b;
    a = fast_segment_remainder(a, b + b);
    if (a <= b) return a;
    return a - b;
}

auto fast_segment_gcm(line_segment a, line_segment b) {
    while (a != b) {
        a = fast_segment_remainder(a, b);
        std::swap(a, b);
    }
    return a;
}

// Section 4.5

auto fast_segment_remainder1(line_segment a, line_segment b) {
    // precondition: b != 0
    if (a < b) return a;
    if (a - b < b) return a - b;
    a = fast_segment_remainder1(a, b + b);
    if (a < b) return a;
    return a - b;
}

auto largest_doubling(line_segment a, line_segment b) {
    // precondition: b != 0
    while (a - b >= b) b = b + b;
    return b;
}

auto remainder(line_segment a, line_segment b) {
    // precondition: b != 0
    if (a < b) return a;
    auto c = largest_doubling(a, b);
    a = a - c;
    while (c != b) {
        c = half(c);
        if (c <= a) a = a - c;
    }
    return a;
}

auto quotient(line_segment a, line_segment b) {
    // Precondition: b > 0
    if (a < b) return integer(0);
    auto c = largest_doubling(a, b);
    integer n{1};
    a = a - c;
    while (c != b) {
        c = half(c); n = n + n;
        if (c <= a) { a = a - c; n = n + 1; }
    }
    return n;
}

auto quotient_remainder(line_segment a, line_segment b) {
    // Precondition: b > 0
    if (a < b) return std::make_pair(integer(0), a);
    line_segment c = largest_doubling(a, b);
    integer n(1);
    a = a - c;
    while (c != b) {
        c = half(c); n = n + n;
        if (c <= a) { a = a - c; n = n + 1; }
    }
    return std::make_pair(n, a);
}

auto remainder_fibonacci(line_segment a, line_segment b) {
    // Precondition: b > 0
    if (a < b) return a;
    auto c = b;
    do {
        auto tmp = c; c = b + c; b = tmp;
    } while (a >= c);
    do {
        if (a >= b) a = a - b;
        auto tmp = c - b; c = b; b = tmp;
    } while (b < c);
    return a;
}

auto gcm_remainder(line_segment a, line_segment b) {
    while (b != line_segment(0)) {
        a = remainder(a, b);
        std::swap(a, b);
    }
    return a;
}

auto gcd(integer a, integer b) {
    while (b != integer(0)) {
        a = a % b;
        std::swap(a, b);
    }
    return a;
}
