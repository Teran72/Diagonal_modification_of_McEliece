#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
#include "galois.hpp"
#include "matrix.hpp"
#include "goppa.hpp"
#include "crypto.hpp"

using namespace std;
using namespace galois;
using namespace matrix;
using namespace goppa;
using namespace crypto;



Goppa_public::Goppa_public() {}

Goppa_public::Goppa_public(int t, const Matrix<Galois>& G)
	: t(t)
	, G(G) {}

Goppa_public::~Goppa_public() {}

Matrix<Galois> Goppa_public::encode(const Matrix<Galois>& message) const {
	int k = G.size(0);
	int n = message.size(1);

	Matrix<Galois> m(1, k);
	for (int i = 0; i < k; ++i) {
		m(0, i) = (i < n) ? message(0, i) : Galois(0, 3);
	}

	return m * G;
}

Matrix<Galois> Goppa_public::get_G() const {
	return G;
}

int Goppa_public::get_n() const {
	return G.size(1);
}

int Goppa_public::get_k() const {
	return G.size(0);
}

int Goppa_public::get_t() const {
	return t;
}

Matrix<Galois> Goppa_public::add_errors(const Matrix<Galois>& y) const {
	int n = y.size(1);
	vector<Galois> err(0);
	for (int i = 0; i < n; i++) {
		err.push_back(Galois((i < t) ? 1 : 0, 3));
	}
	random_shuffle(err.begin(), err.end());
	return y + (Matrix<Galois>)err;
}



Goppa_private::Goppa_private() {}

Goppa_private::Goppa_private(unsigned int poly, const Matrix<Galois>& g, const Matrix<Galois>& H,
	const Matrix<Galois>& Y, const Matrix<Galois>& G_inv, const vector<int>& L_nums)
	: poly(poly)
	, g(g)
	, H(H)
	, Y(Y)
	, G_inv(G_inv)
	, L_nums(L_nums) {}

Goppa_private::~Goppa_private() {}

Matrix<Galois> Goppa_private::decode(const Matrix<Galois>& _y) const {
	Galois::stash_global_poly(poly);
	int n = _y.size(1);
	int t = H.size(0);
	Matrix<Galois> y = _y;
	Matrix<Galois> theta;
	for (int i = 0; i < n; i++) {
		y(0, i).copy_poly(H(0, 0));
	}
	
	bool is_code_word;
	while (1) {
		theta = H * y.transpose();
		is_code_word = true;
		for (int i = 0; i < t; i++) {
			if (!theta(i, 0).isZero()) {
				 is_code_word = false;
				 break;
			}
		}
		if (is_code_word) {
			break;
		}

		Matrix<Galois> T(t, t);
		Galois coeff = theta(t - 1, 0) * g(0, t).inv();
		T(0, 0) = Galois(1, poly) - g(0, 0) * coeff;
		for (int i = 1; i < t; i++) {
			T(i, 0) = theta(i - 1, 0) - g(0, i) * coeff;
		}
		for (int j = 1; j < t; j++) {
			coeff = T(t - 1, j - 1) * g(0, t).inv();
			T(0, j) = -g(0, 0) * coeff;
			for (int i = 1; i < t; i++) {
				T(i, j) = T(i - 1, j - 1) - g(0, i) * coeff;
			}
		}

		for (int i = 0; i < t; i++) {
			if (i & 1) {
				T(i, i) += Galois(1, poly);
			}
		}

		bool nonsingular = T.safe_inv();
		if (!nonsingular) {
			for (int i = 0; i < n; i++) {
				if (L_nums[i] == -1) {
					y(0, i) += Galois(1, poly);
					break;
				}
			}
		} else {
			theta = T * theta;
			break;
		}
	}

	if (is_code_word) {
		for (int i = 0; i < n; i++) {
			y(0, i).copy_poly(G_inv(0, 0));
		}
		Galois::unstash_global_poly();
		return y * G_inv;
	}

	Matrix<Galois> u(1, t + 1);
	u(0, 0) = Galois(1, poly);
	for (int i = 0; i < t; i++) {
		u(0, i + 1) = theta(i, 0);
	}
	u = u * Y;
	for (int i = 0; i < n; i++) {
		if (u(0, i).isZero()) {
			y(0, i) += Galois(1, poly);
		}
		y(0, i).copy_poly(G_inv(0, 0));
	}

	Galois::unstash_global_poly();

	return y * G_inv;
}




Goppa::Goppa(const string &filename)
	: filename(filename) {}

Goppa::~Goppa() {};

void Goppa::generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k) const {
	ifstream info(filename);
	int t;
	unsigned int poly;
	int n;

	info >> t >> poly;
	Matrix<Galois> g(1, t + 1);

	Galois::stash_global_poly(poly);
	for (int i = 0; i <= t; i++) {
		info >> g(0, i);
	}

	info >> n;
	vector<int> L_nums(n);
	vector<Galois> L(n);
	for (int i = 0; i < n; i++) {
		info >> L_nums[i];
		if (L_nums[i] == -1) {
			L[i] = Galois(0, poly);
		} else {
			L[i] = Galois(1, poly);
			for (int j = 0; j < L_nums[i]; j++) {
				L[i] *= Galois(2, poly);
			}
		}
	}

	info.close();

	Matrix<Galois> X(t, t);
	Matrix<Galois> Y(t + 1, n);
	Matrix<Galois> Z(n, n);

	for (int i = 0; i < t; i++) {
		for (int j = 0; j < t; j++) {
			X(i, j) = (i + j < t) ? g(0, i + j + 1) : Galois(0, poly);
		}
	}

	for (int j = 0; j < n; j++) {
		Y(0, j) = Galois(1, poly);
	}
	for (int i = 1; i <= t; i++) {
		for (int j = 0; j < n; j++) {
			Y(i, j) = Y(i - 1, j) * L[j];
		}
	}
	Matrix<Galois> h = g * Y;

	for (int i = 0; i < n; i++) {
		Z(i, i) = h(0, i).inv();
	}

	Matrix<Galois> H = X * Y.submatrix(0, t, 0, n) * Z;

	Galois::unstash_global_poly();
	Galois::stash_global_poly(3);

	int m = 0;
	while (poly >> m) {
		m++;
	}
	m--;
	Matrix<Galois> G(m * t, n);
	for (int i = 0; i < t; i++) {
		for (int j = 0; j < n; j++) {
			unsigned int val = H(i, j).get_val();
			for (int k = 0; k < m; k++) {
				G(i * m + k, j) = Galois(((val >> k) & 1), 3);
			}
		}
	}
	G = G.repair();
	G.inv();
	G = G.transpose();
	G = G.submatrix(t * m, n, 0, n);
	G = Matrix<Galois>::randInvertible(n - t * m) * G;

	*pub_k = new Goppa_public(t, G);

	int k = n - m * t;
	
	G = G.transpose();
	G.hconcat(Matrix<Galois>(n));
	G.eliminate(false, k);
	G = G.submatrix(0, k, k, k + n).transpose();
	
	*priv_k = new Goppa_private(poly, g, H, Y, G, L_nums);

	Galois::unstash_global_poly();
}
