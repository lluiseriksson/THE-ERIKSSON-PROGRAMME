// Independent exact leading-minor calculation. Input is a rational p/q,
// shift s, and maximum polynomial degree. Output gives each pivot sign.
#include <gmpxx.h>
#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <vector>
using Z = mpz_class;

Z choose(unsigned n, unsigned k) {
    Z b;
    mpz_bin_uiui(b.get_mpz_t(), n, k);
    return b;
}

Z power(unsigned b, unsigned e) {
    Z v;
    mpz_ui_pow_ui(v.get_mpz_t(), b, e);
    return v;
}

int main() {
    unsigned p,q,s,n;
    while (std::cin >> p >> q >> s >> n) {
        if (q==0 || p>q || s>1 || n>100) throw std::runtime_error("input");
        std::vector<Z> moments(2*n+s+1);
        for(unsigned k=0;k<moments.size();++k)
            for(unsigned j=0;j<=k;++j) {
                Z term=choose(k,j)*choose(k+j,j);
                moments[k]+=term*term*power(p,j)*power(q,k-j);
            }
        std::vector<std::vector<Z>> h(n+1,std::vector<Z>(n+1));
        for(unsigned i=0;i<=n;++i)
            for(unsigned j=i;j<=n;++j) h[i][j]=moments[i+j+s];
        Z divisor=1;
        for(unsigned k=0;k<=n;++k) {
            Z pivot=h[k][k];
            std::cout << mpz_sgn(pivot.get_mpz_t()) << ' ';
            if(pivot<=0) break;
            for(unsigned i=k+1;i<=n;++i)
                for(unsigned j=i;j<=n;++j) {
                    Z num=pivot*h[i][j]-h[k][i]*h[k][j];
                    if (!mpz_divisible_p(num.get_mpz_t(),divisor.get_mpz_t()))
                        throw std::runtime_error("nonexact Bareiss division");
                    mpz_divexact(h[i][j].get_mpz_t(),num.get_mpz_t(),divisor.get_mpz_t());
                }
            divisor=pivot;
        }
        std::cout << '\n';
    }
}