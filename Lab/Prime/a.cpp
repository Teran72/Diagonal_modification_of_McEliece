#include <iostream>

using namespace std;

bool is_prime(int n) {
	for (int i = 2; i * i <= n; i++) {
		if (n % i == 0) {
			return 0;
		}
	}
	return 1;
}

int check(int n, int k = 2) {
	int p = 1;
	for (int i = 0; i < n; i++) {
		p = p * k % n;
	}
	p = (p + n - k) % n;
	return p;
}

int main() {
	freopen("pr.data.out", "w", stdout);

	for (int i = 2; i < 10000; i++) {
		int a = is_prime(i);
		int b = check(i, 2);
//		cout << i << " " << a << " " << b;
		if ((a == 0 && b == 0) || (a != 0 && b != 0)) {
			cout << i << " " << a << " " << b;
			cout << " alarm!!!!!!!";
			cout << "\n";
		}
//		cout << "\n";
	}
	
	return 0;
}
