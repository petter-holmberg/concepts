// concepts.h

// Copyright (c) 2017 Petter Holmberg
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.


// Concepts from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#ifndef EOP_CONCEPTS
#define EOP_CONCEPTS

#include <type_traits>

// For types X and Y, Same<X, Y> is true iff X and Y
// denote exactly the same type after elimination of aliases.
template <class T, class U>
concept bool Same() {
    return std::is_same<T, U>::value;
}

template <class T>
concept bool Destructible() {
    return requires (T t, const T ct, T* p) {
        { t.~T() } noexcept;
        { &t } -> Same<T*>; // Not required to be equality preserving.
        { &ct } -> Same<const T*>; // Not required to be equality preserving.
        delete p;
        delete[] p;
    };
}

namespace {

template <class T, class ...Args>
concept bool __ConstructibleObject = // exposition only
    Destructible<T>() && requires (Args&& ...args) {
        T{std::forward<Args>(args)...}; // not required to be equality preserving
        new T{std::forward<Args>(args)...}; // not required to be equality preserving
    };

template <class T, class ...Args>
concept bool __BindableReference = // exposition only
    std::is_reference<T>::value && requires (Args&& ...args) {
        T(std::forward<Args>(args)...);
    };

} // namespace

template <class T, class ...Args>
concept bool Constructible() {
    return __ConstructibleObject<T, Args...> || __BindableReference<T, Args...>;
}

// For types X and Y, ConvertibleTo<X, Y> is true iff X can be implicitly converted to Y.
template <class T, class U>
concept bool ConvertibleTo() {
    return std::is_convertible<T, U>::value;
}

template <class T>
concept bool MoveConstructible() {
    return Constructible<T, std::remove_cv_t<T>&&>()
        && ConvertibleTo<std::remove_cv_t<T>&&, T>();
}

template <class T>
concept bool CopyConstructible() {
    return MoveConstructible<T>()
        && Constructible<T, const std::remove_cv_t<T>&>()
        && ConvertibleTo<std::remove_cv_t<T>&, T>()
        && ConvertibleTo<const std::remove_cv_t<T>&, T>()
        && ConvertibleTo<const std::remove_cv_t<T>&&, T>();
}

// For types X and Y, Common<X, Y> is true iff X and Y can both be
// unambiguously converted to a common type Z.
template <class T, class U>
concept bool Common() {
    return requires (T t, U u) {
        typename std::common_type_t<T, U>;
        typename std::common_type_t<U, T>;
        requires Same<std::common_type_t<U, T>, std::common_type_t<T, U>>();
        std::common_type_t<T, U>(std::forward<T>(t));
        std::common_type_t<T, U>(std::forward<U>(u));
        // axiom (T t1, T t2, U u1, U u2) {
        //     using C = std::common_type_t<T, U>;
        //     eq (t1, t2) <=> eq(C{t1}, C{t2});
        //     eq (u1, u2) <=> eq(C{u1}, C{u2});
        // }
    };
}

template <class T, class U>
concept bool Assignable() {
    return Common<T, U>() && requires(T&& a, U&& b) {
        { std::forward<T>(a) = std::forward<U>(b) } -> Same<T&>;
    };
}

template <class T>
concept bool Swappable() {
    return requires(T&& a, T&& b) {
        std::swap(std::forward<T>(a), std::forward<T>(b));
    };
}

template <class T, class U>
concept bool Swappable() {
    return Swappable<T>()
        && Swappable<U>()
        && Common<T, U>()
        && requires(T&& t, U&& u) {
            std::swap(std::forward<T>(t), std::forward<U>(u));
            std::swap(std::forward<U>(u), std::forward<T>(t));
        };
}

template <class T>
concept bool Movable() {
    return MoveConstructible<T>()
        && Assignable<T&, T&&>()
        && Swappable<T&>();
    // axiom move_semantics {
    //     eq(a, b) => eq(T{std::move(a)}, b);
    //     eq(b, c) => eq(a = std::move(b), c);
    // }
}

template <class F, class...Args>
concept bool Callable() {
    return CopyConstructible<F>()
        && requires (F f, Args&&...args) {
            invoke(f, std::forward<Args>(args)...); // Not required to be equality preserving.
        };
}

template <class F, class...Args>
concept bool RegularCallable() {
    return Callable<F, Args...>();
    // axiom (F f, Args... args) {
    //     equality_preserving(f(args...));
    // }
}

template <class Op, class T>
concept bool BinaryOperation() {
    return RegularCallable<Op, T, T>() && ConvertibleTo<std::result_of_t<Op(T, T)>, T>();
}

template <class T>
concept bool Copyable() {
    return CopyConstructible<T>()
        && Movable<T>()
        && Assignable<T&, const T&>();
    // axiom copy_semantics {
    //     eq(T{a}, a);
    //     eq(a = b, b);
    // }
}

template <class T>
concept bool DefaultConstructible() {
    return Constructible<T>()
        && requires (const size_t n) {
            new T[n]{}; // Not required to be equality preserving.
        };
}

template <class T>
concept bool Semiregular() {
    return Copyable<T>() && DefaultConstructible<T>();
}

template <class B>
concept bool Boolean() {
    return MoveConstructible<B>()
        && requires(const B b1, const B b2, const bool a) {
            bool(b1);
            { b1 } -> bool;
            bool(!b1);
            { !b1 } -> bool;
            { b1 && b2 } -> Same<bool>;
            { b1 && a } -> Same<bool>;
            { a && b1 } -> Same<bool>;
            { b1 || b2 } -> Same<bool>;
            { b1 || a } -> Same<bool>;
            { a || b1 } -> Same<bool>;
            { b1 == b2 } -> bool;
            { b1 != b2 } -> bool;
            { b1 == a } -> bool;
            { a == b1 } -> bool;
            { b1 != a } -> bool;
            { a != b1 } -> bool;
        };
}

template <class T, class U>
concept bool WeaklyEqualityComparable() {
    return requires(const T t, const U u) {
        { t == u } -> Boolean;
        { u == t } -> Boolean;
        { t != u } -> Boolean;
        { u != t } -> Boolean;
    };
    // axiom { t == u <=> eq(t, u); }
    // axiom {
    //    t == t;
    //    t == u => u == t;
    //    t == u && u == c => t == c;
    // }
    // axiom { t != u <=> !(t == u); }
}

template <class T>
concept bool EqualityComparable() {
    return WeaklyEqualityComparable<T, T>();
}

template <class T>
concept bool Regular() {
    return Semiregular<T>() && EqualityComparable<T>();
}

#endif // EOP_CONCEPTS
