#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>
using I=std::int64_t;
using Pair=std::array<int,2>;
bool compatible(int a,int b,int c,int d,int v) {
    if(b==0)b=1;
    if(d==0)d=1;
    if(1000LL*(I(a)*d+I(c)*b)<(2LL*v-1)*b*d)return false;
    const I B=1000LL*b+1,D=1000LL*d+1;
    return 1000000LL*(a*D+c*B)<=(2LL*v+1)*B*D;
}
using Buckets=std::vector<std::vector<Pair>>;
Buckets counts(int p,int r,int f) {
    Buckets ok(355*234);
    for(int a=0;a<=376;++a) for(int c=0;c<=266;++c) {
        if(!compatible(a,376,c,266,r))continue;
        for(int x=0;x<=354;++x)for(int y=0;y<=233;++y){
            if(compatible(a,a+x,c,c+y,p)&&compatible(2*a,376+a+x,2*c,266+c+y,f))
                ok[234*x+y].push_back({a,c});
        }
    }
    return ok;
}
int main(){
    std::array<int,6> v;
    while(std::cin>>v[0]>>v[1]>>v[2]>>v[3]>>v[4]>>v[5]){
        auto det=counts(v[0],v[1],v[2]),cor=counts(v[3],v[4],v[5]);
        std::array<int,6> witness{};I hits=0;
        for(int k=0;k<355*234;++k)for(auto t:det[k])for(auto c:cor[k])
            if(c[0]<=t[0]&&c[1]<=t[1]){
                if(!hits)witness={t[0],t[1],c[0],c[1],k/234,k%234};
                ++hits;
            }
        std::cout<<hits;
        for(int x:witness)std::cout<<" "<<x;
        std::cout<<"\n";
    }
}
