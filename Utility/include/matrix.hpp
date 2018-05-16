#ifndef MATRIX
#define MATRIX

#include <iostream>
#include <vector>
#include <stdexcept>

/*
namespace matrix {
	template <class eltype>
	struct Matrix {
	public:
		explicit Matrix(int m, int n);
		explicit Matrix(int m = 0);
		Matrix(const std::vector<eltype>& vec);
		Matrix(const Matrix<eltype>& matrix);
		Matrix<eltype>& operator=(const Matrix<eltype>& matrix);
		~Matrix();
		int size(int axis) const;
		eltype operator()(int i, int j) const;
		eltype& operator()(int i, int j);
		Matrix<eltype> submatrix(int m0, int m1, int n0, int n1) const;
		void hconcat(const Matrix<eltype>& matrix);
		void vconcat(const Matrix<eltype>& matrix);
		void flip(int axis);
		Matrix<eltype> transpose() const;
		Matrix<eltype>& operator+=(const Matrix<eltype>& matrix);
		Matrix<eltype>& operator-=(const Matrix<eltype>& matrix);
		Matrix<eltype>& operator*=(const Matrix<eltype>& matrix);
		Matrix<eltype>& operator*=(const eltype& l);
		void eliminate(bool oneway = false, int maxj = n);
		Matrix<eltype> repair() const;
		void inv();
		bool safe_inv();
		Matrix<eltype> operator+() const;
		Matrix<eltype> operator-() const;
		bool isZero() const;
		bool compare(const Matrix& matrix) const;
		void write(std::ostream* outStream = &std::cout) const;
		void read(std::istream* inStream = &std::cin);
		static Matrix<eltype> randInvertible(int n);
	private:
		int m, n;
		std::vector<std::vector<eltype> > vals;
	};
	Matrix<eltype> operator+(Matrix<eltype> a, Matrix<eltype> const& b);
	Matrix<eltype> operator-(Matrix<eltype> a, Matrix<eltype> const& b);
	Matrix<eltype> operator*(Matrix<eltype> a, Matrix<eltype> const& b);
	Matrix<eltype> operator*(Matrix<eltype> a, eltype const& l);
	bool operator==(const Matrix<eltype>& a, const Matrix<eltype>& b);
	bool operator!=(const Matrix<eltype>& a, const Matrix<eltype>& b);
	std::ostream& operator<<(std::ostream& outStream, const Matrix<eltype>& matrix);
	std::istream& operator>>(std::istream& inStream, Matrix<eltype>& matrix);
} // matrix
*/

namespace matrix {

	template <class eltype>
	struct Matrix {
	public:
		explicit Matrix(int m, int n)
			: m(m)
			, n(n) {
			vals = std::vector<std::vector<eltype> >(m, std::vector<eltype> (n, 0));
		}

		explicit Matrix(int m = 0)
			: Matrix(m, m) {
			for (int i = 0; i < m; ++i) {
				vals[i][i] = 1;
			}
		}

		Matrix(const std::vector<eltype>& vec)
			: Matrix(1, vec.size()) {
			for (int j = 0; j < n; ++j) {
				vals[0][j] = vec[j];
			}
		}

		Matrix(const Matrix<eltype>& matrix)
			: m(matrix.m)
			, n(matrix.n) {
			vals = std::vector<std::vector<eltype> >(m, std::vector<eltype>(n));
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					vals[i][j] = matrix.vals[i][j];
				}
			}
		}

		Matrix<eltype>& operator=(const Matrix<eltype>& matrix) {
			if (&matrix != this) {
				m = matrix.m;
				n = matrix.n;
				vals = std::vector<std::vector<eltype> >(m, std::vector<eltype>(n));
				for (int i = 0; i < m; ++i) {
					for (int j = 0; j < n; ++j) {
						vals[i][j] = matrix.vals[i][j];
					}
				}
			}
			return *this;
		}

		~Matrix() {}

		int size(int axis) const {
			return (axis & 1 ? n : m);
		}

		eltype operator()(int i, int j) const {
			if (i < 0 || m < i || j < 0 || n < j) {
				throw std::domain_error("Index is out of range");
			}
			return vals[i][j];
		}

		eltype& operator()(int i, int j) {
			if (i < 0 || m < i || j < 0 || n < j) {
				throw std::domain_error("Index is out of range");
			}
			return vals[i][j];
		}

		Matrix<eltype> submatrix(int m0, int m1, int n0, int n1) const {
			Matrix<eltype> res(m1 - m0, n1 - n0);
			for (int i = 0; i < m1 - m0; ++i) {
				for (int j = 0; j < n1 - n0; ++j) {
					res.vals[i][j] = vals[m0 + i][n0 + j];
				}
			}
			return res;
		}

		void hconcat(const Matrix<eltype>& matrix) {
			if (m != matrix.m) {
				throw std::domain_error("Matrix sizes don't match");
			}
			for (int i = 0; i < m; ++i) {
				vals[i].resize(n + matrix.n);
				for (int j = 0; j < matrix.n; ++j) {
					vals[i][n + j] = matrix.vals[i][j];
				}
			}
			n += matrix.n;
		}

		void vconcat(const Matrix<eltype>& matrix) {
			if (n != matrix.n) {
				throw std::domain_error("Matrix sizes don't match");
			}
			vals.resize(m + matrix.m, std::vector<eltype>(n));
			for (int i = 0; i < matrix.m; ++i) {
				for (int j = 0; j < n; ++j) {
					vals[m + i][j] = matrix.vals[i][j];
				}
			}
			m += matrix.m;
		}

		void flip(int axis) {
			if (axis & 1) {
				for (int i = 0; i < m; ++ i) {
					for (int j = 0; 2 * j < n - 1; ++j) {
						eltype temp = vals[i][j];
						vals[i][j] = vals[i][n - j - 1];
						vals[i][n - j - 1] = temp;
					}
				}
			} else {
				for (int i = 0; 2 * i < m - 1; ++ i) {
					for (int j = 0; j < n; ++j) {
						eltype temp = vals[i][j];
						vals[i][j] = vals[m - i - 1][j];
						vals[m - i - 1][j] = temp;
					}
				}
			}
		}

		Matrix<eltype> transpose() const {
			Matrix<eltype> ans(n, m);
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					ans(j, i) = vals[i][j];
				}
			}
			return ans;
		}

		Matrix<eltype>& operator+=(const Matrix<eltype>& matrix) {
			if (m != matrix.m || n != matrix.n) {
				throw std::domain_error("Matrix sizes don't match");
			}
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					vals[i][j] += matrix.vals[i][j];
				}
			}
			return *this;
		}

		Matrix<eltype>& operator-=(const Matrix<eltype>& matrix) {
			if (m != matrix.m || n != matrix.n) {
				throw std::domain_error("Matrix sizes don't match");
			}
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					vals[i][j] -= matrix.vals[i][j];
				}
			}
			return *this;
		}

		Matrix<eltype>& operator*=(const Matrix<eltype>& matrix) {
			if (n != matrix.m) {
				throw std::domain_error("Matrix sizes don't match");
			}
			for (int i = 0; i < m; ++i) {
				std::vector<eltype> line(matrix.n);
				for (int j = 0; j < matrix.n; ++j) {
					eltype sum = 0;
					for (int k = 0; k < n; ++k) {
						sum += vals[i][k] * matrix.vals[k][j];
					}
					line[j] = sum;
				}
				vals[i] = line;
			}
			n = matrix.n;
			return *this;
		}

		Matrix<eltype>& operator*=(const eltype& l) {
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					vals[i][j] *= l;
				}
			}
			return *this;
		}

		void eliminate(bool oneway = false, int maxj = -1) {
			if (maxj < 0) {
				maxj = n;
			}
			int pos = 0;
			for (int j = 0; j < n && j < maxj; ++j) {
				int next;
				for (next = pos; next < m && vals[next][j] == 0; ++next) {}
				if (next == m) {
					continue;
				}

				for (int k = j; k < n; ++k) {
					eltype t = vals[pos][k];
					vals[pos][k] = vals[next][k];
					vals[next][k] = t;
				}

				for (int k = n - 1; k >= j; --k) {
					vals[pos][k] /= vals[pos][j];
				}

				int begin = oneway ? pos + 1 : 0;
				for (int i = begin; i < m; ++i) {
					if (i == pos) {
						continue;
					}
					eltype coeff = vals[i][j];
					for (int k = j; k < n; ++k) {
						vals[i][k] -= coeff * vals[pos][k];
					}
				}
				pos++;
			}
		}

		Matrix<eltype> repair() const {
			int l = m;
			Matrix<eltype> M_1_til = *this;
			M_1_til.eliminate(true);
			Matrix<eltype> M_2_til = Matrix<eltype>(n - l, n);

			int r = 0;
			int nr = 0;
			for (int j = 0; j < n; ++j) {
				if (r < l && M_1_til(r, j) != 0) {
					r++;
				} else {
					M_2_til(nr, j) = 1;
					nr++;
				}
			}
			M_1_til = *this;
			M_1_til.vconcat(M_2_til);
			return M_1_til;
		}


		void inv() {
			if (m != n) {
				throw std::domain_error("Matrix is not square");
			}

			this->hconcat(Matrix<eltype>(m));
			this->eliminate(false, m);

			for (int i = 0; i < m; ++i) {
				if (vals[i][i] != 1) {
					throw std::domain_error("Matrix is not invertible");
				}
			}
			*this = this->submatrix(0, m, m, 2 * m);
		}

		bool safe_inv() {
			if (m != n) {
				throw std::domain_error("Matrix is not square");
			}
			this->hconcat(Matrix<eltype>(m));
			this->eliminate(false, m);

			bool ans = true;
			for (int i = 0; i < m; ++i) {
				if (vals[i][i] == 0) {
					ans = false;
					break;
				}
			}
			*this = this->submatrix(0, m, m, 2 * m);
			return ans;
		}

		Matrix<eltype> operator+() const {
			return *this;
		}

		Matrix<eltype> operator-() const {
			Matrix<eltype> res(*this);
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					res.vals[i][j] = -res.vals[i][j];
				}
			}
			return res;
		}

		bool isZero() const {
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					if (!vals[i][j].isZero()) {
						return false;
					}
				}
			}
			return true;
		}

		bool compare(const Matrix& matrix) const {
			if (m != matrix.m || n != matrix.n) {
				return false;
			}
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					if (vals[i][j] != matrix.vals[i][j]) {
						return false;
					}
				}
			}
			return true;
		}

		void write(std::ostream* outStream = &std::cout) const {
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j, (*outStream) << " ") {
					(*outStream) << vals[i][j];
				}
				(*outStream) << "\n";
			}
		}

		void read(std::istream* inStream = &std::cin) {
			(*inStream) >> m >> n;
			vals = std::vector<std::vector<eltype> >(m, std::vector<eltype>(n));
			for (int i = 0; i < m; ++i) {
				for (int j = 0; j < n; ++j) {
					(*inStream) >> vals[i][j];
				}
			}
		}

		static Matrix<eltype> randInvertible(int n) {
			Matrix<eltype> A(n, n);
			Matrix<eltype> T(n, n);

			std::vector<int> indices(n + 1);
			for (int i = 0; i < n + 1; ++i) {
				indices[i] = i;
			}

			for (int i = 0; i < n; ++i) {
				std::vector<eltype> row(n - i);
				int cnt = 0;
				while (cnt == 0) {
					for (int j = 0; j < n - i; ++j) {
						row[j] = eltype::rand();
						if (row[j] != 0) {
							cnt++;
						}
					}
				}

				int r = indices[0];
				int prev = 0;
				for (int p = 0; row[p] == 0; ++p) {
					prev = r + 1;
					r = indices[r + 1];
				}

				A(i, r) = 1;
				for (int j = i + 1; j < n; ++j) {
					A(j, r) = eltype::rand();
				}
				int pos = indices[0];
				for (int j = 0; j < n - i; ++j, pos = indices[pos + 1]) {
					T(r, pos) = row[j];
				}

				indices[prev] = indices[r + 1];
			}
			return A * T;
		}

	private:
		int m, n;
		std::vector<std::vector<eltype> > vals;
	};

	template <class eltype>
	Matrix<eltype> operator+(Matrix<eltype> a, Matrix<eltype> const& b) {
		return a += b;
	}

	template <class eltype>
	Matrix<eltype> operator-(Matrix<eltype> a, Matrix<eltype> const& b) {
		return a -= b;
	}

	template <class eltype>
	Matrix<eltype> operator*(Matrix<eltype> a, Matrix<eltype> const& b) {
		return a *= b;
	}

	template <class eltype>
	Matrix<eltype> operator*(Matrix<eltype> a, eltype const& l) {
		return a *= l;
	}

	template <class eltype>
	bool operator==(const Matrix<eltype>& a, const Matrix<eltype>& b) {
		return a.compare(b);
	}

	template <class eltype>
	bool operator!=(const Matrix<eltype>& a, const Matrix<eltype>& b) {
		return !a.compare(b);
	}

	template <class eltype>
	std::ostream& operator<<(std::ostream& outStream, const Matrix<eltype>& matrix) {
		matrix.write(&outStream);
		return outStream;
	}

	template <class eltype>
	std::istream& operator>>(std::istream& inStream, Matrix<eltype>& matrix) {
		matrix.read(&inStream);
		return inStream;
	}

} // matrix

#endif // !MATRIX
