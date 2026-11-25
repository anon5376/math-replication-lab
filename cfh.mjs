export function result(q, m = q**4n) {
if (m < 0n || m > q**4n) throw RangeError("m must be in [0,q^4]");
const nCk=(n,k)=>{if(k<0||BigInt(k)>n)return 0n; let a=1n;for(let j=1;j<=k;j++)a=a*(n-BigInt(j-1))/BigInt(j);return a};
const G=(n,k)=>{if(k<0||k>n)return 0n;let a=1n,b=1n;for(let j=0;j<k;j++){a*=q**BigInt(n-j)-1n;b*=q**BigInt(k-j)-1n;}if(a%b)throw Error("bad Gaussian");return a/b};
const b=m*q**12n;
const chain=(d,t,rs,i=0,p=0,s=0)=>{
 if(i===rs.length)return 1n;
 let v=0n, delta=rs[i]-p-s;
 for(let u=0;u<=Math.min(d-p,delta);u++){
 let w=delta-u; if(BigInt(w)<=t-BigInt(s))v+=G(d-p,u)*nCk(t-BigInt(s),w)*chain(d,t,rs,i+1,p+u,s+w);
 }return v;
};
const ranks=mask=>[1,2,3,4].filter((_,i)=>mask&(1<<i));
const flag=Array.from({length:16},(_,mask)=>{
 const rs=ranks(mask);
 if(!(mask&8))return chain(8,m,rs);
 const inner=rs.slice(0,-1);
 return chain(8,m,rs)+b*(chain(4,1n,inner)-chain(4,0n,inner)-G(4,3)*chain(3,1n,inner));
});
const beta=flag.slice();
for(let bit=1;bit<=8;bit*=2)for(let mask=0;mask<=15;mask++)if(mask&bit)beta[mask]-=beta[mask^bit];
const disc=([a,c,d])=>c*c-4n*a*d;
const h=[beta[15],beta[14]+beta[13]+beta[11],beta[10]];
const f=[h[0],h[1]+beta[7],h[2]+beta[6]+beta[5]];
return {h,f,D:[disc(h),disc(f)]};
}
