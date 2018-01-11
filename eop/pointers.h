// pointers.h

// Copyright (c) 2009 Alexander Stepanov and Paul McJones
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.


// Definitions of type functions and global functions from concepts
// Readable, Writeable, Mutable, Iterator, BidirectionalIterator
// for types const T& and pointer(T) from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#pragma once

#include "intrinsics.h"
#include "type_functions.h"

#include <cstddef> // ptrdiff_t


template <typename T>
    __requires(Regular(T))
struct value_type<Pointer<T>>
{
    typedef T type;
};

template <typename T>
    __requires(Regular(T))
const T& source(Pointer<T> x)
{
    return *x;
}

template <typename T>
    __requires(Regular(T))
const T& source(const T& x)
{
    return x;
}

template <typename T>
    __requires(Regular(T))
struct distance_type<Pointer<T>>
{
    typedef ptrdiff_t type;
};

template<typename T>
    __requires(Regular(T))
auto successor(Pointer<T> x) -> Pointer<T>
{
    return x + ptrdiff_t(1);
}

template <typename T>
    __requires(Regular(T))
auto predecessor(Pointer<T> x) -> Pointer<T>
{
    return x - ptrdiff_t(1);
}

template <typename T>
    __requires(Regular(T))
auto sink(Pointer<T> x) -> T&
{
    return *x;
}

template <typename T>
    __requires(Regular(T))
auto sink(T& x) -> T&
{
    return x;
}

template <typename T>
    __requires(Regular(T))
auto deref(Pointer<T> x) -> T&
{
    return *x;
}

//template <typename T>
//    __requires(Regular(T))
//T& deref(T& x)
//{
//    return x;
//}

template <typename T>
    __requires(Regular(T))
struct iterator_concept<T*>
{
    typedef random_access_iterator_tag __concept;
};

