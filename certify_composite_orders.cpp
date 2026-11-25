#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using I = int64_t;
using V = std::vector<I>;
I mul(I a,I b,I p){return a*b%p;}
I add(I a,I b,I p){I r=a+b;return r>=p?r-p:r;}
I sub(I a,I b,I p){I r=a-b;return r<0?r+p:r;}
I pw(I a,I n,I p){I r=1;while(n){if(n&1)r=mul(r,a,p);a=mul(a,a,p);n/=2;}return r;}
bool prime(I p){if(p<2)return false;if(p%2==0)return p==2;for(I j=3;j*j<=p;j+=2)if(p%j==0)return false;return true;}
V pf(I d){V a;for(I r=2;r*r<=d;r++)if(d%r==0){a.push_back(r);while(d%r==0)d/=r;}if(d>1)a.push_back(d);return a;}
bool exact_order(I w,I d,I p){if(w<1||w>=p||(p-1)%d||pw(w,d,p)!=1)return false;for(I r:pf(d))if(pw(w,d/r,p)==1)return false;return true;}
void trim(V& a){while(!a.empty()&&a.back()==0)a.pop_back();}
V gcd(V a,V b,I p){
 trim(a);trim(b);
 while(!b.empty()){
  I t=pw(b.back(),p-2,p);
  while(a.size()>=b.size()){
   size_t z=a.size()-b.size();I q=mul(a.back(),t,p);
   for(size_t j=0;j+1<b.size();j++)a[z+j]=sub(a[z+j],mul(q,b[j],p),p);
   a.pop_back();trim(a);
  }
  a.swap(b);
 }
 if(!a.empty()){I iv=pw(a.back(),p-2,p);for(I& u:a)u=mul(u,iv,p);}
 return a;
}
I eval(const V& a,I x,I p){I y=0;for(auto i=a.rbegin();i!=a.rend();i++)y=add(mul(y,x,p),*i,p);return y;}
// Method 1: coefficient q-Pascal + explicit evaluation at every fixed node.
// Method 2: contiguous q-Pochhammer ratios + polynomial Euclid on z^d+1.
bool certify(I d,I p,I w,int method){
 if(!prime(p)||!exact_order(w,d,p)||!(d&1))return false;
 V powers(d+1,1),units(d),inverses(d),h{1},F(d+1,0);
 F[0]=F[d]=1;for(I j=1;j<=d;j++)powers[j]=mul(powers[j-1],w,p);
 if(method==2)for(I k=1;k<d;k++){units[k]=sub(1,powers[k],p);inverses[k]=pw(units[k],p-2,p);}
 for(I b=1;b<d;b++){
  V g(b+1,1);
  for(I k=1;k<b;k++)g[k]=method==1?add(h[k],mul(powers[b-k],h[k-1],p),p):mul(mul(g[k-1],units[b-k+1],p),inverses[k],p);
  if(method==2&&mul(mul(g[b-1],units[1],p),inverses[b],p)!=1) return false;
  V der(b);
  for(I k=1;k<=b;k++)der[k-1]=mul(k,g[k],p);
  if(gcd(g,der,p)!=V{1})return false;
  if(method==1){
   for(I j=0;j<d;j++)if((eval(g,p-powers[j],p)==0)!=((b&1)&&j==0))return false;
  }else if(gcd(F,g,p)!=(b&1?V{1,1}:V{1}))return false;
  h.swap(g);
 }
 return true;
}
// Verifies the complete bundled witness table for all 76 certified odd composite orders.
// Bounds on p keep signed 64-bit products exact.
int main(int argc,char* argv[]){
 if(argc!=2){std::cerr<<"Usage: certify_composite_orders composite_witnesses.csv\n";return 2;}
 V orders;for(I d=9;d<=255;d+=2)if(!prime(d))orders.push_back(d);
 orders.push_back(289);orders.push_back(343);
 std::ifstream in(argv[1]);
 std::string line;
 if(!std::getline(in,line)||line!="d,ell1,w1,ell2,w2"){
  std::cerr<<"Missing or malformed CSV header\n";return 1;
 }
 I count=0;
 for(I expected:orders){
  I d=0,p=0,w=0,p2=0,w2=0;char c1,c2,c3,c4;
  if(!std::getline(in,line)){std::cerr<<"Missing row "<<expected<<"\n";return 1;}
  std::istringstream row(line);std::string extra;
  if(!(row>>d>>c1>>p>>c2>>w>>c3>>p2>>c4>>w2)||
     c1!=','||c2!=','||c3!=','||c4!=','||(row>>extra)||
     d!=expected||p==p2||p<2||p2<2||p>2000000||p2>2000000||
     !certify(d,p,w,1)||!certify(d,p2,w2,2)){
   std::cerr<<"Witness replay failed for "<<expected<<"\n";return 1;
  }
  count+=d-1;
 }
 if(in>>line){std::cerr<<"Extra CSV rows\n";return 1;}
 if(orders.size()!=76||count!=10860)return 1;
 std::cout<<"PASS: "<<orders.size()<<" orders; "<<count
          <<" nonconstant residuals; "<<2*count<<" exact checks (two witnesses)\n";
}
