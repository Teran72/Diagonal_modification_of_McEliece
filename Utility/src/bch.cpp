#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <tuple>
#include <algorithm>
#include "galois.hpp"
#include "matrix.hpp"
#include "bch.hpp"
#include "crypto.hpp"

using namespace std;
using namespace galois;
using namespace matrix;
using namespace bch;
using namespace crypto;



BCH_public::BCH_public() {}

BCH_public::BCH_public(int t, const Matrix<Galois>& G_0)
	: t(t)
	, G_0(G_0) {}

BCH_public::~BCH_public() {}

Matrix<Galois> BCH_public::encode(const Matrix<Galois>& message) const {
	int k = G_0.size(0);
	int n = message.size(1);

	Matrix<Galois> m(1, k);
	for (int i = 0; i < k; ++i) {
		m(0, i) = (i < n) ? message(0, i) : Galois(0, 3);
	}

	return m * G_0;
}

Matrix<Galois> BCH_public::get_G() const {
	return G_0;
}

int BCH_public::get_n() const {
	return G_0.size(1);
}

int BCH_public::get_k() const {
	return G_0.size(0);
}

int BCH_public::get_t() const {
	return t;
}

Matrix<Galois> BCH_public::add_errors(const Matrix<Galois>& y) const {
	int n = y.size(1);
	vector<Galois> err(0);
	for (int i = 0; i < n; i++) {
		err.push_back(Galois((i < t) ? 1 : 0, 3));
	}
	random_shuffle(err.begin(), err.end());
//	cout << y;
//	cout << (y + (Matrix<Galois>)err) << "\n";
	return y + (Matrix<Galois>)err;

}




BCH_private::BCH_private() {}

BCH_private::BCH_private(int t, unsigned int poly, const Matrix<Galois>& G_0_inv)
	: t(t)
	, poly(poly)
	, G_0_inv(G_0_inv) {}

BCH_private::~BCH_private() {}

Matrix<Galois> BCH_private::decode(const Matrix<Galois>& y) const {
	Galois::stash_global_poly(poly);

	Matrix<Galois> s(2 * t, 1);

	Matrix<Galois> alpha(2 * t, 1);

	alpha(0, 0) = Galois(2, poly);
	s(0, 0) = Galois(0, poly);
	for (int i = 1; i < 2 * t; i++) {
		alpha(i, 0) = alpha(i - 1, 0) * alpha(0, 0);
		s(i, 0) = Galois(0, poly);
	}

	int n = y.size(1);
	for (int j = 0; j < n; j++) {
		Galois y_val = y(0, j);
		y_val.copy_poly(s(0, 0));

		for (int i = 0; i < 2 * t; i++) {
			s(i, 0) *= alpha(i, 0);
			s(i, 0) += y_val;
		}
	}

	bool is_code_word = true;
	for (int i = 0; i < 2 * t; i++) {
		if (!s(i, 0).isZero()) {
			is_code_word = false;
			break;
		}
	}

	if (is_code_word) {
		Galois::unstash_global_poly();
		return y * G_0_inv;
	}

//	cout << "s =\n" << s << endl;

	Matrix<Galois> S(t);
	for (int i = 0; i < t; i++) {
		for (int j = 0; j < t; j++) {
			S(i, j) = s(i + j, 0);
		}
	}

//	cout << "S = " << S << endl;

	Matrix<Galois> ds(t, 1);
	for (int i = 0; i < t; i++) {
		ds(i, 0) = -s(i + t, 0);
	}
	S.inv();

	Matrix<Galois> sig = S * ds;

	Matrix<Galois> x(y);
	Galois alp(1, poly);
	for (int i = 0; i < n; i++) {
		Galois val(0, poly);
		for (int j = 0; j < t; j++) {
			val += sig(j, 0);
			val *= alp;
		}
		val += Galois(1, poly);
		if (val.isZero()) {
			x(0, (n - 1 + i) % n) += Galois(1, 3);
		}
		alp *= Galois(2, poly);
	}

	Galois::unstash_global_poly();

	return x * G_0_inv;
}




BCH::BCH(int n)
	: n(n) {
	if (this->n != 7 && this->n != 63) {
		this->n = 7;
	}	
}

BCH::~BCH() {};

void BCH::generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k) const {
	stringstream ss;
	ss << ".bch" << n;
	string filename = ss.str();

	unsigned int pol;
	int h;

	ifstream bchinfo(filename);
	int t;
	int nn;
	bchinfo >> nn >> pol >> t >> h;
	Galois::stash_global_poly(3);

	vector<vector<Galois> > gs;

	for (int i = 0; i < h; i++) {
		gs.push_back(vector<Galois>(0));
		int len;
		bchinfo >> len;
		for (int j = 0; j < len; j++) {
			int temp;
			bchinfo >> temp;
			gs[i].push_back(Galois(temp));
		}
	}

	bchinfo.close();

	vector<Galois> g = mulPolynoms(gs, n);
	Matrix<Galois> G_0 = make_bch(g);
	int k = G_0.size(0);

	*pub_k = new BCH_public(t, G_0);
	
	G_0 = G_0.transpose();
	G_0.hconcat(Matrix<Galois>(n));
	G_0.eliminate(true, k);
	
	*priv_k = new BCH_private(t, pol, G_0.submatrix(0, k, k, k + n).transpose());

	Galois::unstash_global_poly();
}



Matrix<Galois> BCH::make_bch(const vector<Galois>& g) {
	int n = g.size();
	int k;
	for (k = 1; g[n - k] == 0; ++k) {}
	Matrix<Galois> res(k, n);

	for (int i = 0; i < k; ++i) {
		for (int j = 0; j < n; ++j) {
			//res(i, j) = g[(j + i) % n];
			//res(i, (j + i) % n) = g[j];
			res(i, (n + n - k - j + i) % n) = g[j];
		}
	}
	return res;
}

vector<Galois> BCH::mulPolynoms(const vector<vector<Galois> >& gs, int n) {
	vector<Galois> res = {1};
	for (int i = 0; i < (int) gs.size(); ++i) {
		vector<Galois> temp(res.size() + gs[i].size() - 1, 0);
		for (int j = 0; j < (int) gs[i].size(); ++j) {
			for (int k = 0; k < (int) res.size(); ++k) {
				temp[j + k] += gs[i][j] * res[k];
			}
		}
		res = temp;
	}
	while ((int) res.size() < n) {
		res.push_back(0);
	}
	return res;
}
