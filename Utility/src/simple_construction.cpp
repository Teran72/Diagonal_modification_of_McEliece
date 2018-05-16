#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <tuple>
#include <algorithm>
#include "galois.hpp"
#include "matrix.hpp"
#include "simple_construction.hpp"
#include "crypto.hpp"

using namespace std;
using namespace galois;
using namespace matrix;
using namespace crypto;
using namespace simple_construction;

Simple_public::Simple_public() {}

Simple_public::Simple_public(int t, const Matrix<Galois>& G, const Matrix<Galois>& M_1)
	: t(t)
	, G(G)
	, M_1(M_1) {}

Simple_public::~Simple_public() {}

Matrix<Galois> Simple_public::encode(const Matrix<Galois>& message) const {
	int k = G.size(0);
	int n = message.size(1);

	Matrix<Galois> m(1, k);
	for (int i = 0; i < k; ++i) {
		m(0, i) = (i < n) ? message(0, i) : Galois(0, 3);
	}

	m *= G;
	n = m.size(1);

	int p = M_1.size(0);

	vector<Galois> err(0);
	for (int i = 0; i < p; i++) {
		err.push_back(Galois((i < t) ? 1 : 0, 3));
	}
	random_shuffle(err.begin(), err.end());
	Matrix<Galois> merr = (Matrix<Galois>)err;
	merr *= M_1;
	return m + merr;
}

Matrix<Galois> Simple_public::get_G() const {
	return G;
}

Matrix<Galois> Simple_public::get_M_1() const {
	return M_1;
}

int Simple_public::get_n() const {
	return G.size(1);
}

int Simple_public::get_k() const {
	return G.size(0);
}
int Simple_public::get_t() const {
	return t;
}




Simple_private::Simple_private() {}

Simple_private::Simple_private(const Matrix<Galois>& M_inv,
			const Crypto_private_key* decoder)
	: M_inv(M_inv)
	, decoder(decoder) {}

Simple_private::~Simple_private() {}

Matrix<Galois> Simple_private::decode(const Matrix<Galois>& y) const {
	Matrix<Galois> ans;
	ans = y * M_inv;

	ans = decoder->decode(ans);

	return ans;
}




Simple::Simple(const Cryptosystem &_decoder) {
	decoder = &_decoder;
}

Simple::~Simple() {}

void Simple::generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k) const {
	Crypto_public_key *inner_pub_k;
	Crypto_private_key *inner_priv_k;
	
	decoder->generate_pair(&inner_pub_k, &inner_priv_k);

	Matrix<Galois> G_0 = inner_pub_k->get_G();
	int n = G_0.size(1);
	int k = G_0.size(0);
	int t = inner_pub_k->get_t();
	int p = n - k / 2;

	Galois::stash_global_poly(3);
	Matrix<Galois> M = Matrix<Galois>::randInvertible(n);
	Matrix<Galois> M_1 = M.submatrix(0, p, 0, n);

	G_0 = G_0 * M;

	M.inv();

	*pub_k = new Simple_public(t, G_0, M_1);
	*priv_k = new Simple_private(M, inner_priv_k);
	delete inner_pub_k;

	Galois::unstash_global_poly();
}
