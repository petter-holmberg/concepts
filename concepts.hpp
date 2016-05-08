#pragma once

#include <cstdlib>
#include <type_traits>
#include <utility>

// Core language concepts:

// For types X and Y, Same<X, Y> is true iff X and Y
// denote exactly the same type after elimination of aliases.
template <class T, class U>
concept bool Same() {
    return std::is_same<T, U>::value;
}

// For types X and Y, DerivedFrom<X, Y> is true iff Y is a base class of X.
template <class T, class U>
concept bool DerivedFrom() {
    return std::is_base_of<U, T>::value;
}

// For types X and Y, ConvertibleTo<X, Y> is true iff X can be implicitly converted to Y.
template <class T, class U>
concept bool ConvertibleTo() {
    return std::is_convertible<T, U>::value;
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

// Type classification defined by the standard.
template <class T>
concept bool Integral() {
    return std::is_integral<T>::value;
}

// Type classification defined by the standard.
template <class T>
concept bool SignedIntegral() {
    return Integral<T>() && std::is_signed<T>::value;
}

// Type classification defined by the standard.
template <class T>
concept bool UnsignedIntegral() {
    return Integral<T>() && !SignedIntegral<T>();
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
    return Swappable<T>() &&
        Swappable<U>() &&
        Common<T, U>() &&
        requires(T&& t, U&& u) {
            std::swap(std::forward<T>(t), std::forward<U>(u));
            std::swap(std::forward<U>(u), std::forward<T>(t));
        };
}

// Object concepts:

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
concept bool __ConstructibleObject = // Exposition only.
    Destructible<T>() && requires (Args&& ...args) {
        T{std::forward<Args>(args)...}; // Not required to be equality preserving.
        new T{std::forward<Args>(args)...}; // Not required to be equality preserving.
    };

template <class T, class ...Args>
concept bool __BindableReference = // Exposition only.
    std::is_reference<T>::value && requires (Args&& ...args) {
        T(std::forward<Args>(args)...);
    };

}

template <class T, class ...Args>
concept bool Constructible() {
    return __ConstructibleObject<T, Args...> || __BindableReference<T, Args...>;
}

template <class T>
concept bool DefaultConstructible() {
    return Constructible<T>() &&
        requires (const size_t n) {
            new T[n]{}; // Not required to be equality preserving.
        };
}

template <class T>
concept bool MoveConstructible() {
    return Constructible<T, std::remove_cv_t<T>&&>() &&
        ConvertibleTo<std::remove_cv_t<T>&&, T>();
}


template <class T>
concept bool CopyConstructible() {
    return MoveConstructible<T>() &&
        Constructible<T, const std::remove_cv_t<T>&>() &&
        ConvertibleTo<std::remove_cv_t<T>&, T>() &&
        ConvertibleTo<const std::remove_cv_t<T>&, T>() &&
        ConvertibleTo<const std::remove_cv_t<T>&&, T>();
}

template <class T>
concept bool Movable() {
    return MoveConstructible<T>() &&
        Assignable<T&, T&&>() &&
        Swappable<T&>();
    // axiom move_semantics {
    //     eq(a, b) => eq(T{std::move(a)}, b);
    //     eq(b, c) => eq(a = std::move(b), c);
    // }
}

template <class T>
concept bool Copyable() {
    return CopyConstructible<T>() &&
        Movable<T>() &&
        Assignable<T&, const T&>();
    // axiom copy_semantics {
    //     eq(T{a}, a);
    //     eq(a = b, b);
    // }
}

// Foundational and comparison concepts:

template <class B>
concept bool Boolean() {
    return MoveConstructible<B>() &&
        requires(const B b1, const B b2, const bool a) {
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

template <class T, class U>
concept bool EqualityComparable() {
    return Common<T, U>() &&
        EqualityComparable<T>() &&
        EqualityComparable<U>() &&
        EqualityComparable<std::common_type_t<T, U>>() &&
        WeaklyEqualityComparable<T, U>();
}

template <class T>
concept bool StrictTotallyOrdered() {
    return EqualityComparable<T>() &&
    requires (const T a, const T b) {
        { a < b } -> Boolean;
        { a > b } -> Boolean;
        { a <= b } -> Boolean;
        { a >= b } -> Boolean;
        // axiom {
        //     !(a < a);
        //     a < b => !(b < a);
        //     a < b && b < c => a < c;
        //     a < b || b < a || a == b;
        // }
        // axiom {
        //     a > b <=> b < a;
        //     a <= b <=> !(b < a);
        //     a >= b <=> !(b > a);
        // }
    };

}

template <class T, class U>
concept bool StrictTotallyOrdered() {
    return Common<T, U>() &&
        StrictTotallyOrdered<T>() &&
        StrictTotallyOrdered<U>() &&
        StrictTotallyOrdered<std::common_type_t<T, U>>() &&
        EqualityComparable<T, U>() &&
        requires (const T t, const U u) {
            { t < u } -> Boolean;
            { t > u } -> Boolean;
            { t <= u } -> Boolean;
            { t >= u } -> Boolean;
            { u < t } -> Boolean;
            { u > t } -> Boolean;
            { u <= t } -> Boolean;
            { u >= t } -> Boolean;
        };
}

template <class T>
concept bool Semiregular() {
    return Copyable<T>() &&
    DefaultConstructible<T>();
}

template <class T>
concept bool Regular() {
    return Semiregular<T>() &&
    EqualityComparable<T>();
}

// Callable concepts:

template <class F, class...Args>
concept bool Callable() {
    return CopyConstructible<F>() &&
        requires (F f, Args&&...args) {
            invoke(f, std::forward<Args>(args)...); // not required to be equality preserving
        };
}

template <class F, class...Args>
concept bool RegularCallable() {
    return Callable<F, Args...>();
}

template <class F, class...Args>
concept bool Predicate() {
    return RegularCallable<F, Args...>() &&
        Boolean<std::result_of_t<F&(Args...)>>();
}

template <class R, class T>
concept bool Relation() {
    return Predicate<R, T, T>();
}

template <class R, class T, class U>
concept bool Relation() {
    return Relation<R, T>() &&
        Relation<R, U>() &&
        Common<T, U>() &&
        Relation<R, std::common_type_t<T, U>>() &&
        Predicate<R, T, U>() &&
        Predicate<R, U, T>();
        // axiom {
        //     using C = CommonType<T, U>;
        //     r(t, u) <=> r(C{t}, C{u});
        //     r(u, t) <=> r(C{u}, C{t});
        // }
}

template <class R, class T>
concept bool StrictWeakOrder() {
    return Relation<R, T>();
}

template <class R, class T, class U>
concept bool StrictWeakOrder() {
    return Relation<R, T, U>();
}

// Operations:

template <class Op, class T>
concept bool UnaryOperation() {
    return RegularCallable<Op, T>() &&
        ConvertibleTo<std::result_of_t<Op(T)>, T>();
}

template <class Op, class T>
concept bool BinaryOperation() {
    return RegularCallable<Op, T, T>() &&
        ConvertibleTo<std::result_of_t<Op(T, T)>, T>();
}

template <class Op, class T, class U>
concept bool BinaryOperation() {
    return BinaryOperation<Op, T>() &&
    BinaryOperation<Op, U>() &&
    Common<T, U>() &&
    BinaryOperation<Op, Common<T, U>>() &&
    requires (Op op, T a, U b) {
        { op(a, b) } -> std::common_type_t<T, U>();
        { op(b, a) } -> std::common_type_t<T, U>();
        // axiom {
        //     eq(op(a, b), op(C{a}, C{b}));
        //     eq(op(b, a), op(C{b}, C{a}));
        // }
    };
}

// Iterator concepts:

template <class>
struct value_type {};

template <class T>
struct value_type<T*>: std::enable_if<std::is_object<T>::value, std::remove_cv_t<T>> {};

template<class I>
    requires std::is_array<I>::value
struct value_type<I>: value_type<std::decay_t<I>> {};

template <class I>
struct value_type<I const>: value_type<std::decay_t<I>> {};

template <class T>
    requires requires { typename T::value_type; }
struct value_type<T>: std::enable_if<std::is_object<typename T::value_type>::value, typename T::value_type> {};

template <class T>
requires requires { typename T::element_type; }
struct value_type<T>: std::enable_if<std::is_object<typename T::element_type>::value, typename T::element_type> {};

template <class T>
using value_type_t = typename value_type<T>::type;

template <class I>
concept bool Readable() {
    return Semiregular<I>() &&
        requires (const I i) {
        typename value_type_t<I>;
        { *i } -> const value_type_t<I>&; // pre: i is dereferenceable
    };
}

template <class Out, class T>
concept bool Writable() {
    return Semiregular<Out>() &&
        requires(Out o, T&& v) {
        *o = std::forward<T>(v); // not required to be equality preserving
        // axiom {
        //     Readable<Out> && Same<ValueType<Out>, T> =>
        //         (is_valid(*o = value) => (*o = value, eq(*o, value)));
        // }
    };
}
