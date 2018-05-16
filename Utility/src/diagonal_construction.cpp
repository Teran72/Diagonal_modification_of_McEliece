#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <tuple>
#include <algorithm>
#include "galois.hpp"
#include "matrix.hpp"
#include "diagonal_construction.hpp"
#include "crypto.hpp"

using namespace std;
using namespace galois;
using namespace matrix;
using namespace crypto;
using namespace diagonal_construction;

Diagonal_public::Diagonal_public() {}

Diagonal_public::Diagonal_public(const Matrix<Galois>& _G, const Matrix<Galois>& _W)
	: t(0) {
	G = _G;
	W = _W;
}

Diagonal_public::~Diagonal_public() {}

Matrix<Galois> Diagonal_public::encode(const Matrix<Galois>& message) const {
	int k = G.size(0);
	int n = message.size(1);

	Matrix<Galois> m(1, k);
	for (int i = 0; i < k; ++i) {
		m(0, i) = (i < n) ? message(0, i) : Galois(0, 3);
	}

	m *= G;
	n = m.size(1);

	vector<Galois> err(0);
	for (int i = 0; i < n; i++) {
		err.push_back(Galois((rand() & 1) ? 1 : 0, 3));
	}
	Matrix<Galois> merr = (Matrix<Galois>)err;
	merr *= W;

//	cout << "merr = " << merr << endl;
	return m + merr;
}

Matrix<Galois> Diagonal_public::get_G() const {
	return G;
}

Matrix<Galois> Diagonal_public::get_W() const {
	return W;
}

int Diagonal_public::get_n() const {
	return G.size(1);
}

int Diagonal_public::get_k() const {
	return G.size(0);
}
int Diagonal_public::get_t() const {
	return t;
}




Diagonal_private::Diagonal_private() {}

Diagonal_private::Diagonal_private(const Matrix<Galois>& M_inv,
			const Crypto_private_key* decoder)
	: M_inv(M_inv)
	, decoder(decoder) {}

Diagonal_private::~Diagonal_private() {}

Matrix<Galois> Diagonal_private::decode(const Matrix<Galois>& y) const {
	Matrix<Galois> ans;
	ans = y * M_inv;

	ans = decoder->decode(ans);

	return ans;
}




Diagonal::Diagonal(const Cryptosystem &_decoder) {
	decoder = &_decoder;
}

Diagonal::~Diagonal() {}

void Diagonal::generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k) const {
	Crypto_public_key *inner_pub_k;
	Crypto_private_key *inner_priv_k;
	
	decoder->generate_pair(&inner_pub_k, &inner_priv_k);

	Matrix<Galois> G_0 = inner_pub_k->get_G();
	int n = G_0.size(1);
	int t = inner_pub_k->get_t();

	Galois::stash_global_poly(3);
	Matrix<Galois> M = Matrix<Galois>::randInvertible(n);
	Matrix<Galois> D = Matrix<Galois>(n);
	Matrix<Galois> V = Matrix<Galois>::randInvertible(n);

	vector<Galois> err(0);
	for (int i = 0; i < n; i++) {
		err.push_back(Galois((i < t) ? 1 : 0, 3));
	}
	random_shuffle(err.begin(), err.end());
	for (int i = 0; i < n; i++) {
		D(i, i) = err[i];
	}

	V = V * D * M;

	G_0 = G_0 * M;

	M.inv();

	*pub_k = new Diagonal_public(G_0, V);
	*priv_k = new Diagonal_private(M, inner_priv_k);
	delete inner_pub_k;

	Galois::unstash_global_poly();
}
