#include <array>
#include <iostream>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>

using Small = __int128_t;
using Big = boost::multiprecision::int256_t;
using Pair = std::array<int,2>;
using Witness = std::array<int,6>;
struct Ratio { Small n,d; };

// Equal language weights, scores in tenths of a percent, epsilon = 1/10^8.
Ratio mean_rate(int a,int b,int c,int d) {
    const Small scale=100000000;
    Small B=scale*b+1, D=scale*d+1;
    return {500*scale*(a*D+c*B), B*D};
}
template<class T> bool in_cell(T n,T d,int bin) {
    return (2*bin-1)*d<=2*n && 2*n<=(2*bin+1)*d;
}
using Buckets=std::vector<std::vector<Pair>>;
Buckets feasible(int p,int r,int f) {
    Buckets out(355*234);
    for(int a=0;a<=376;a++) for(int c=0;c<=266;c++) {
        Ratio R=mean_rate(a,376,c,266);
        if(!in_cell(R.n,R.d,r))continue;
        for(int x=0;x<=354;x++) for(int y=0;y<=233;y++) {
            Ratio P=mean_rate(a,a+x,c,c+y);
            if(!in_cell(P.n,P.d,p))continue;
            Big n=2*Big(P.n)*Big(R.n),d=Big(P.n)*Big(R.d)+Big(R.n)*Big(P.d);
            if(d==0) d=1;
            if(in_cell(n,d,f))out[234*x+y].push_back({a,c});
        }
    }
    return out;
}
bool less_rate(const Witness &a,const Witness &b) {
    return (a[2]+a[3])*(b[0]+b[1])<(b[2]+b[3])*(a[0]+a[1]);
}
int main() {
    std::array<int,6> s;
    while(std::cin>>s[0]>>s[1]>>s[2]>>s[3]>>s[4]>>s[5]) {
        auto detected=feasible(s[0],s[1],s[2]), corrected=feasible(s[3],s[4],s[5]);
        long long count=0; Witness low{},high{};
        for(int k=0;k<355*234;k++)for(auto t:detected[k])for(auto c:corrected[k]){
            if(c[0]>t[0]||c[1]>t[1])continue;
            if(t[0]+t[1]==0)return 3;
            Witness w={t[0],t[1],c[0],c[1],k/234,k%234};
            if(!count||less_rate(w,low))low=w;
            if(!count||less_rate(high,w))high=w;
            for(int n:w)std::cout<<n<<' ';
            std::cout<<'\n';
            ++count;
        }
        std::cout<<"END "<<count;
        for(int n:low)std::cout<<' '<<n;
        for(int n:high)std::cout<<' '<<n;
        std::cout<<'\n';
    }
}