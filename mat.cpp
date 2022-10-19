#include <iostream>
#include <sstream>
#include <iomanip>
#include <array>

template <int m, int n, typename t = int>
requires (m > 0 && n > 0)
struct matrix : public std::array<std::array<t, n>, m> {
    matrix<n,m,t> transpose() const {
        matrix<n,m,t> ret{};
        for (auto i = 0; i < m; i++)
            for (auto j = 0; j < n; j++)
                ret[j][i] = (*this)[i][j];
        return ret;
    }

    matrix<m,n,t>& operator*=(t scalar) {
        for (auto i = 0; i < m; i++)
            for (auto j = 0; j < n; j++)
                (*this)[j][i] += scalar;
        return *this;
    }

    template <typename s>
    matrix<m,n,decltype(t{} * s{})> operator*(s scalar) const {
        matrix<m,n,decltype(t{} * s{})> ret{};
        for (auto i = 0; i < m; i++)
            for (auto j = 0; j < n; j++)
                ret[i][j] = (*this)[i][j] * scalar;
        return ret;
    }

    template <int o, typename t2>
    matrix<m,o,decltype(t{} * t2{})> operator*(const matrix<n,o,t2>& rhs) const {
        matrix<m,o,decltype(t{} * t2{})> ret{};
        for (auto i = 0; i < m; i++) {
            for (auto j = 0; j < n; j++) {
                for (auto k = 0; k < o; k++) {
                    ret[i][k] += (*this)[i][j] * rhs[j][k];
                }
            }
        }
        return ret;
    }

    template <typename t2>
    matrix<m,n,t>& operator*=(const matrix<n,n,t2>& rhs) {
        // can't avoid the temp copy regardless
        *this = *this * rhs;
        return *this;
    }

    matrix<m,n,t> operator+(const matrix<m,n,t>& other) const {
        auto mat = *this;
        mat += other;
        return mat;
    }

    matrix<m,n,t> operator+=(const matrix<m,n,t>& other) {
        for (auto i = 0; i < m; i++)
            for (auto j = 0; j < n; j++)
                (*this)[j][i] += other[i][j];
        return *this;
    }

    template <typename q = void>
    requires (m > 1 && n > 1)
    auto minor(int a, int b) const {
        a = std::clamp(a, 0, m-1);
        b = std::clamp(b, 0, n-1);

        matrix<m-1,n-1,t> ret{};

        for (auto i = 0; i < a; i++) {
            for (auto j = 0; j < b; j++)
                ret[i][j] += (*this)[i][j];
            for (auto j = b + 1; j < n; j++)
                ret[i][j-1] += (*this)[i][j];
        }
        for (auto i = a + 1; i < m; i++) {
            for (auto j = 0; j < b; j++)
                ret[i-1][j] += (*this)[i][j];
            for (auto j = b + 1; j < n; j++)
                ret[i-1][j-1] += (*this)[i][j];
        }
        return ret;
    }

    template <typename q = void>
    requires (m == n)
    t trace() const {
        t ret{};
        for (auto i = 0; i < m; i++)
            ret += (*this)[i][i];
        return ret;
    }

    template <typename q = void>
    requires (m == n)
    t determinant() const {
        // special cases up to 3x3 should be a bit faster in the most common cases
        if constexpr (m == 1)
            return (*this)[0][0];
        if constexpr (m == 2)
            return (*this)[0][0] * (*this)[1][1] - (*this)[1][0] * (*this)[0][1];
        if constexpr (m == 3)
            return + (*this)[0][0] * (*this)[1][1] * (*this)[2][2]  // + a e i
                   + (*this)[0][1] * (*this)[1][2] * (*this)[2][0]  // + b f g
                   + (*this)[0][2] * (*this)[1][0] * (*this)[2][1]  // + c d h
                   - (*this)[0][2] * (*this)[1][1] * (*this)[2][0]  // - c e g
                   - (*this)[0][0] * (*this)[1][2] * (*this)[2][1]  // - a f h
                   - (*this)[0][1] * (*this)[1][0] * (*this)[2][2]; // - b d i

        if constexpr (m > 3) { // templates are dumb
            t ret{};
            for (auto j = 0; j < m; j++)
                ret += (*this)[0][j] * cofactor(0,j);
            return ret;
        }
    }

    template <typename q = void>
    requires (m == n && m > 1)
    t cofactor(int a, int b) const {
        a = std::clamp(a, 0, m-1);
        b = std::clamp(b, 0, n-1);
        auto sign = (a + b) % 2 == 0 ? 1 : -1;
        return sign * minor(a,b).determinant();
    }

    auto cofactor() const {
        matrix<m,n,t> ret;
        for (auto i = 0; i < m; i++)
            for (auto j = 0; j < n; j++)
                ret[i][j] = cofactor(i, j);
        return ret;
    }

    bool invertible() const {
        return determinant() != 0;
    }

    auto adjugate() const {
        return cofactor().transpose();
    }

    template <int m2, int n2, typename t2>
    bool operator==(const matrix<m2,n2,t2>& mat) const {
        if constexpr (m != m2 || n != n2) {
            return false;
        }
        else {
            if (&mat == this)
                return true;
            for (auto i = 0; i < m; i++)
                for (auto j = 0; j < n; j++)
                    if (mat[i][j] != (*this)[i][j])
                        return false;
        }
        return true;
    }

    template <typename t2>
    operator matrix<m,n,t2>() const {
        matrix<m,n,t2> ret;
        for (auto i = 0; i < m; i++)
            for (auto j = 0; j < n; j++)
                ret[i][j] = (*this)[i][j];
        return ret;
    }

    auto inverse() const {
        if constexpr (std::is_floating_point_v<t>)
            return adjugate() * (t{1} / determinant());
        else {
            matrix<m,n,float> ret = *this;
            return ret.adjugate() * (float{1} / ret.determinant());
        }
    }

    template <typename q = void>
    requires (m == n)
    static matrix<m,n,t> identity() {
        matrix<m,n,t> mat{};
        for (auto i = 0; i < m; i++)
            mat[i][i] = 1;
        return mat;
    }
};

template <int m, typename t = int>
struct hvector : public matrix<1, m, t> {};

template <typename t, typename... u>
hvector(t, u...) -> hvector<1 + sizeof...(u), t>;

template <int m, typename t = int>
struct vvector : public matrix<m, 1, t> {};

template <typename t, typename... u>
vvector(t, u...) -> vvector<1 + sizeof...(u), t>;

template<int m, int n, typename t>
std::ostream& print_mat(std::ostream& stream, const matrix<m,n,t>& mat) {
    std::array<int,n> widths{};

    for (auto& row : mat) {
        for (auto j = 0; j < n; j++) {
            // std::to_string prints floats differently
            std::stringstream ss;
            ss << row[j];
            int x = ss.str().size();
            if (widths[j] < x)
                widths[j] = x;
        }
    }

    if constexpr (m == 1) {
        stream << "[";
        for (const auto& i : mat[0])
            stream << " " << i;
        return stream << " ]\n";
    }
    
    stream << "┌";
    auto firstline = mat.front();
    for (auto j = 0; j < n; j++)
        stream << " " << std::setw(widths[j]) << firstline[j];
    stream << " ┐\n";

    for (auto i = 1u; i < mat.size() - 1; i++) {
        stream << "│";
        for (auto j = 0; j < n; j++)
            stream << " " << std::setw(widths[j]) << mat[i][j];
        stream << " │\n";
    }

    stream << "└";
    auto lastline = mat.back();
    for (auto j = 0; j < n; j++)
        stream << " " << std::setw(widths[j]) << lastline[j];
    stream << " ┘\n";

    return stream;
}

template <typename T>
constexpr auto type_name() {
    // these all need to be constexpr string_views for the static_assert to work
#ifdef __clang__
    constexpr std::string_view name = __PRETTY_FUNCTION__;
    constexpr std::string_view prefix = "auto type_name() [T = ";
    constexpr std::string_view suffix = "]";
#elif defined(__GNUC__)
    constexpr std::string_view name = __PRETTY_FUNCTION__;
    constexpr std::string_view prefix = "constexpr auto type_name() [with T = ";
    constexpr std::string_view suffix = "]";
#elif defined(_MSC_VER)
    constexpr std::string_view name = __FUNCSIG__;
    constexpr std::string_view prefix = "auto __cdecl type_name<";
    constexpr std::string_view suffix = ">(void)";
#endif
    static_assert(name.substr(0, prefix.size()) == prefix);
    static_assert(name.substr(name.size() - suffix.size()) == suffix);

    return name.substr(prefix.size(), name.size() - suffix.size() - prefix.size());
}

template<int m, int n, typename t>
std::ostream& operator<<(std::ostream& stream, const matrix<m,n,t>& mat) {
    stream << type_name<typename std::remove_cvref_t<decltype(mat)>>() << "\n";
    return print_mat(stream, mat);
}

template<int m, typename t>
std::ostream& operator<<(std::ostream& stream, const vvector<m,t>& vec) {
    stream << type_name<typename std::remove_cvref_t<decltype(vec)>>() << "\n";
    matrix<m,1,t> mat = vec;
    return print_mat(stream, mat);
}

template<int m, typename t>
std::ostream& operator<<(std::ostream& stream, const hvector<m,t>& vec) {
    stream << type_name<typename std::remove_cvref_t<decltype(vec)>>() << "\n";
    matrix<1,m,t> mat = vec;
    return print_mat(stream, mat);
}

int main() {
#ifdef __clang__
#pragma clang diagnostic ignored "-Wmissing-braces"
#endif
    matrix<1,1> mat11{ 4 };
    matrix<1,2> mat12{ 2, 5 };
    std::cout << mat11 << mat12;
    std::cout << "\n\n\n";

    {
        matrix<3,2> m { 0, 1, 2, 3, 4, 5 };
        auto minor = m.minor(1,2);
        std::cout << m << ".minor(1,2) = " << minor;
    }
    matrix<2,4> mat24{ 0, 1, 2, 3, 4, 5, 6, 7 };
    std::cout << mat11 << mat12 << mat24;
    std::cout << "\n\n\n";
    std::cout << mat24 << mat24.transpose();
    std::cout << "\n\n\n";
    matrix<3,3> wide{ 0, 10, 200, 3, 4, 5, 6, 7, 8 };
    std::cout << wide << "\n\n\n";

    {
        matrix<3,3> a{ 0, 1, 2, 3, 4, 5, 6, 7, 8 };
        matrix<3,3> b{ 1, 0, 0, 0, 1, 0, 0, 0, 1 };
        std::cout << a << "x\n" << b << "=\n" << a*b;
        std::cout << "a.determinant() = " << a.determinant() << '\n';
    }
    std::cout << "\n\n\n";
    std::cout << mat12 * mat24;
    std::cout << "\n\n\n";

    matrix<1,3> mat13{ 1, 2, 3 };
    matrix<3,1> mat31{ 1, 2, 3 };
    std::cout << mat13 << "x\n" << mat31 << "=\n" << mat13*mat31;
    std::cout << "\n\n\n";

    std::cout << mat31 << "x\n" << mat13 << "=\n" << mat31*mat13;
    std::cout << "\n\n\n";

    std::cout << mat31*mat13 << ".trace() = " << (mat31*mat13).trace() << '\n';
    std::cout << "\n\n\n";


    hvector hv{ 1.f,2.f,3.f };
    vvector vv{ 1.f,2.f,3.f };
    std::cout << hv;
    std::cout << vv;
    std::cout << hv * vv;
    matrix<1,3,float> mat13f{ 1, 2, 3 };
    std::cout << mat13f;
    std::cout << "\n\n\n";


    std::cout << sizeof mat11 << '\n';

    std::cout << matrix<5,5>::identity();
    std::cout << "\n\n\n";

    matrix<1,1> square1{ 1 };
    matrix<2,2> square2{ 1, 2, 3, 4 };
    matrix<3,3> square3{ 1, 2, 3, 4, 5, 6, 7, 80, 9 };
    auto square3copy = square3;
    std::cout << square1 << ".determinant() = " << square1.determinant() << '\n';
    std::cout << square2 << ".determinant() = " << square2.determinant() << '\n';
    std::cout << square3 << ".determinant() = " << square3.determinant() << '\n';
    std::cout << square3 << ".cofactor() = " << square3.cofactor() << '\n';

    std::cout << std::boolalpha << (square1 == square2) << '\n';
    std::cout << std::boolalpha << (square2 == square2) << '\n';
    std::cout << std::boolalpha << (square3 == square3copy) << '\n';
    std::cout << std::boolalpha << (square3 != square3copy) << '\n';

    matrix<3,3> invertible{ 1, 2, 3, 0, 1, 4, 5, 6, 0 };
    std::cout << invertible << ".determinant() = " << invertible.determinant() << '\n';
    std::cout << invertible << ".invertible() = " << invertible.invertible() << '\n';
    std::cout << invertible << ".transpose() = " << invertible.transpose() << '\n';
    std::cout << invertible << ".cofactor() = " << invertible.cofactor() << '\n';
    std::cout << invertible << ".adjugate() = " << invertible.adjugate() << '\n';
    std::cout << invertible << ".inverse() = " << invertible.inverse() << '\n';
    std::cout << invertible << ".inverse().inverse() = " << invertible.inverse().inverse() << '\n';
    std::cout << invertible << ".inverse().determinant() = " << invertible.inverse().determinant() << '\n';

    matrix<3,3> invertedtwice = invertible.inverse().inverse();
    std::cout << "inverted twice = " << invertedtwice << '\n';

    std::cout << "\n\n\n";

    matrix<4,3> left{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 };
    matrix<3,3> right{ 0, 1, 2, 3, 4, 5, 6, 7, 8 };
    std::cout << left << "x\n" << right << "=\n" << (left*right);;
    left *= right;
    std::cout << left;
}
