/// Rational numbers and related operations.
module eris.rational;

import std.numeric : gcd, lcm;
import std.traits : isFloatingPoint;

import eris.core : opCmp, hash_t;


/++
[Reduced-form](https://en.wikipedia.org/wiki/Irreducible_fraction) rational number.

NOTE: The current implementation doesn't even try to deal with overflows (yet).
+/
struct Rational(Z) {
    private Z _numerator = 0;
    private Z _denominator = 1;
    invariant (_denominator > 0, "denominator must always be positive");

    version (D_BetterC) {} else {
        /// Returns this rational number formatted as "numerator/denominator".
        string toString() const {
            import std.conv : to;
            import std.string : format;
            return "%s/%s".format(this.numerator.to!string, this.denominator.to!string);
        }
    }

 pragma(inline):
    /// Reduced-form numerator.
    @property Z numerator() const {
        return this._numerator;
    }

    /// Reduced-form denominator, always positive.
    @property Z denominator() const {
        return this._denominator;
    }

    /// Constructs a Rational from given numerator and (non-zero) denominator.
    this(inout(Z) numerator, inout(Z) denominator = 1) inout
    in (denominator != 0, "denominator must not be zero")
    {
        const bool invert = denominator < 0;
        auto num = invert ? -numerator : numerator;
        auto den = invert ? -denominator : denominator;
        auto divisor = gcd(den, num);
        this._numerator = num / divisor;
        this._denominator = den / divisor;
    }

    /// Assigns an integer value to this rational number.
    void opAssign(Z numerator) {
        this = Rational(numerator);
    }

    /// Compares two rationals based on their reduced form.
    bool opEquals(const(Rational) rhs) const {
        return this.numerator == rhs.numerator
            && this.denominator == rhs.denominator;
    }

    /// ditto
    bool opEquals(Z rhs) const {
        return this.denominator == 1 && this.numerator == rhs;
    }

    /// ditto
    bool opEquals(R)(R rhs) const if (isFloatingPoint!R) {
        return this.opCast!R == rhs;
    }

    size_t toHash() const {
        return (this.numerator.hashOf << (hash_t.sizeof * 8U / 2U)) | this.denominator.hashOf;
    }

    /// Compares two rationals based on their reduced form.
    int opCmp(const(Rational) rhs) const {
        const commonMultiple = lcm(this.denominator, rhs.denominator);
        const lhsNumerator = this.numerator * (commonMultiple / this.denominator);
        const rhsNumerator = rhs.numerator * (commonMultiple / rhs.denominator);
        return lhsNumerator.opCmp(rhsNumerator);
    }

    /// ditto
    int opCmp(Z rhs) const {
        return this.numerator.opCmp(rhs * this.denominator);
    }

    /// ditto
    int opCmp(R)(R rhs) const if (isFloatingPoint!R) {
        return this.opCast!R().opCmp(rhs);
    }

    /// Unary negation.
    Rational opUnary(string op : "-")() const {
        return Rational(-this.numerator, this.denominator);
    }

    /// Arithmetic operations on rationals and (after conversion) integers.
    Rational opBinary(string op : "+")(const(Rational) rhs) const {
        const commonMultiple = lcm(this.denominator, rhs.denominator);
        const lhsMultiple = commonMultiple / this.denominator;
        const rhsMultiple = commonMultiple / rhs.denominator;
        return Rational(
            (this.numerator * lhsMultiple) + (rhs.numerator * rhsMultiple),
            commonMultiple
        );
    }

    /// ditto
    Rational opBinary(string op : "+")(Z rhs) const {
        return Rational(
            this.numerator + (rhs * this.denominator),
            this.denominator
        );
    }

    /// ditto
    Rational opBinaryRight(string op : "+")(Z lhs) const {
        return this + lhs;
    }

    /// ditto
    Rational opBinary(string op : "-")(const(Rational) rhs) const {
        return this + (-rhs);
    }

    /// ditto
    Rational opBinary(string op : "-")(Z rhs) const {
        return this + (-rhs);
    }

    /// ditto
    Rational opBinaryRight(string op : "-")(Z lhs) const {
        return lhs + (-this);
    }

    /// ditto
    Rational opBinary(string op : "*")(const(Rational) rhs) const {
        return Rational(
            this.numerator * rhs.numerator,
            this.denominator * rhs.denominator
        );
    }

    /// ditto
    Rational opBinary(string op : "*")(Z rhs) const {
        return Rational(this.numerator * rhs, this.denominator);
    }

    /// ditto
    Rational opBinaryRight(string op : "*")(Z lhs) const {
        return this * lhs;
    }

    /// ditto
    Rational opBinary(string op : "/")(const(Rational) rhs) const
    in (rhs != 0, "can't divide by zero")
    {
        return this * Rational(rhs.denominator, rhs.numerator);
    }

    /// ditto
    Rational opBinary(string op : "/")(Z rhs) const
    in (rhs != 0, "can't divide by zero")
    {
        return Rational(this.numerator, this.denominator * rhs);
    }

    /// ditto
    Rational opBinaryRight(string op : "/")(Z lhs) const {
        return Rational(lhs) / this;
    }

    /// Casts this rational to a scalar type, usually with loss of precision.
    N opCast(N)() const {
        N num = cast(N)(this.numerator);
        N den = cast(N)(this.denominator);
        return num / den;
    }
}

///
@nogc nothrow pure @safe unittest {
    // rationals can store fractional numbers without precision loss
    alias Ratio = Rational!long;
    auto r = Ratio(3, 4);
    assert(r.numerator == 3);
    assert(r.denominator == 4);

    // but remember that they are always kept in reduced form
    assert(Ratio(6, 4) == Ratio(3, 2));
    auto r2 = -(r * 2);
    assert(r2.numerator == -3);
    assert(r2.denominator == 2);

    // they can be compared with floating-point and integral numbers
    assert(r == 0.75 && 0.75 == r);
    assert(r != 1);
    assert(r < 1 && 1 > r);
    assert(r2 <= -1.5 && -1.5 >= r2);
    assert(r > r2);

    // general arithmetic (and casts) work as expected
    assert(Ratio(-3, 5) + Ratio(2, 3) == Ratio(1, 15));
    assert(Ratio(-3, 14) - Ratio(5, 7) == Ratio(-13, 14));
    assert(Ratio(3, 7) * Ratio(7, 3) == 1 && 1 == Ratio(3, 7) * Ratio(7, 3));
    assert(Ratio(7, 3) / Ratio(2, 3) == Ratio(7, 2));
    assert(cast(int)(2 * (1 + Ratio(42) - 1) / 2) == 42);
}

pure @safe unittest {
    import std.bigint;
    BigInt three = 3, four = 4;
    assert(Rational!BigInt(three, four).toString == "3/4");
}

/// Exploits UFCS to provide fraction-like syntax sugar when initializing Rational numbers.
Rational!Z r(Z)(Z num) {
    return Rational!Z(num);
}

///
@nogc nothrow pure @safe unittest {
    auto ratio = 2 / 4.r;
    assert(ratio == Rational!int(2, 4));
}
