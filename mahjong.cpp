// 国标麻将（Chinese Standard Mahjong）样例程序
// 随机策略
// 作者：ybh1998
// 游戏信息：http://www.botzone.org/games#Chinese-Standard-Mahjong
/*
Bot 得到的输入
    1.你的 Bot 首先会收到一行，其中只有一个数字 n，表示目前是第 n 回合（从 1 开始）。
    2.接下来，是 2 * n - 1 条信息，这些信息由 Bot 从平台获取的信息（request）与 Bot 以前每个回合输出的信息（response）交替组成。
        从 1 开始计数，(1 <= i < n)
            第 2 * i - 1 条信息为第 i 回合 Bot 从平台获取的信息（request），共 n - 1 条
            第 2 * i 条信息为 Bot 在第 i 回合输出的信息（response），共 n - 1 条
            最后一条，即第 2 * n - 1 条信息，为当前回合 Bot 从平台获取的新信息（request）
        每条信息可能是 1 行，也可能是多行，具体格式依游戏而定。
        你的 Bot 需要根据以上信息，推演出当前局面，并给出当前局面下的最好决策。
    3.接下来是data，一行 Bot 上回合保存的信息，最大长度为100KB【注意不会保留在 Log 中】。
    4.接下来是globaldata，一行或多行 Bot 上回合或上次对局保存的全局信息，最大长度为100KB【注意不会保留在 Log 中】。
        可以认为 data 行之后的所有内容都是 globaldata，直到文件结尾。

Bot 应该给出的输出
你的 Bot 应当输出四段数据，以换行符隔开。
    1.首先是本回合你的 Bot 做出的决策，请按照游戏要求输出。一定只占一行。
    2.接下来是debug，一行用于回放时候进行调试的信息，最大长度为1KB【注意会保留在 Log 中】。
    3.接下来是data，一行 Bot 本回合想保存的信息，将在下回合输入，最大长度为100KB【注意不会保留在 Log 中】。
    4.接下来是globaldata，一行或多行 Bot 想保存的全局信息，将会在下回合输入，对局结束后也会保留，最大长度为100KB【注意不会保留在 Log 中】。

*/
#include<map>
#include<cmath>
#include<queue>
#include<cstdio>
#include<string>
#include<vector>
#include<cstring>
#include<sstream>
#include<iostream>
#include<algorithm>
#include<ctime>

#include "MahjongGB/MahjongGB.h"
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
//#include <JsonCPP_modified/jsoncpp/json.h>
#endif

#define SIMPLEIO 1
//由玩家自己定义，0表示JSON交互，1表示简单交互。

using namespace std;
#define mp make_pair
#define db double

vector<string> request, response;
//vector<string> hand;

int getType(const char *s){
    return (s[0]=='W'?0:(s[0]=='B'?1:(s[0]=='T'?2:(s[0]=='F'?3:(s[0]=='J'?4:5)))));;
}
string intToString(int i){
    return (i==0?"W":(i==1?"B":(i==2?"T":(i==3?"F":"J"))));
}
string intToString(int i,int j){
    string tmp=intToString(i);
    tmp=tmp+char('0'+j);
    return tmp;
}

int turnID;
int myID,quan;
int hua[4];//每个人花牌数
int card_cnt[4];//牌墙剩余手牌数
bool isMyTurn;
int tmp[6][11];
int searchtime,lastI,lastJ,errorTime,cannotHuTime;
#define searchtimelimit 4000
bool searchover,rebuild;

class huFa{
    //储存中间张即可
    //标号如23代表c[2][3]即3条
    //包括7小对
    //第一次搜索没组成的副子即在“未凑成”中，之后我们直接枚举处于明牌或者手牌，重新储存胡法
    //即之后判断时，“未凑成”中的数组没用
public:
    int shun[4],ke[4],duizi[7];//未凑成
    int myShun[4],myKe[4],myduizi[7],anGang[4];//手牌 暗杠
    int outShun[4],outKe[4],outGang[4];//吃碰 明杠
    int fuzi[10];
    int tt;
    huFa(){
        for(int i=0;i<4;++i)
            shun[i]=ke[i]=myShun[i]=myKe[i]=anGang[i]\
            =outShun[i]=outKe[i]=outGang[i]=0;
        for(int i=0;i<7;++i) duizi[i]=myduizi[i]=0;
        tt=0;
    }
    void init(){
        for(int i=0;i<4;++i)
            shun[i]=ke[i]=myShun[i]=myKe[i]=anGang[i]\
            =outShun[i]=outKe[i]=outGang[i]=0;
        for(int i=0;i<7;++i) duizi[i]=myduizi[i]=0;
        tt=0;
    }

    void copy(const huFa& a){
        for(int i=0;i<4;++i){
            shun[i]=a.shun[i];ke[i]=a.ke[i];myShun[i]=a.myShun[i];
            myKe[i]=a.myKe[i];anGang[i]=a.anGang[i];
            outShun[i]=a.outShun[i];outKe[i]=a.outKe[i];outGang[i]=a.outGang[i];
        }
        for(int i=0;i<7;++i){
            duizi[i]=a.duizi[i];
            myduizi[i]=a.myduizi[i];
        }
        tt=a.tt;
    }
}plan[50010];
int huCnt,tmphucnt;
huFa TMP;
class CARD{
    public:
    int c[6][11];//万饼条风箭花 
    int shun[6][11],mingKe[6][11],anGang[6][11],mingGang[6][11];//是否有以该牌为中间张的吃的顺子，是否有明刻/杠，是否有暗杠
    int totSize;
    int shouPai[6][11];
    int countOutCard;//本人吃碰杠牌组的数目
    int lastplayer;
    int leastHuCard;//距离胡牌最少的牌数
    int chanceToHu;
    char lastCard[4];
    CARD(){
        totSize=0;
        countOutCard=0;
        leastHuCard=14;
        for(int i=0;i<6;++i)for(int j=0;j<11;++j)
            c[i][j]=0,shun[i][j]=mingKe[i][j]=anGang[i][j]=mingGang[i][j]=shouPai[i][j]=0;
        for(int i=0;i<4;++i) lastCard[i]='\0';
        chanceToHu=0;lastplayer=0;
        lastCard[0]='@';
    }
    void copy(const CARD &a){
        for(int i=0;i<6;++i)for(int j=0;j<11;++j){
            c[i][j]=a.c[i][j];shun[i][j]=a.shun[i][j];mingKe[i][j]=a.mingKe[i][j];
            anGang[i][j]=a.anGang[i][j];mingGang[i][j]=a.mingGang[i][j];
            shouPai[i][j]=a.shouPai[i][j];
            totSize=a.totSize;countOutCard=a.countOutCard;
            lastplayer=a.lastplayer;leastHuCard=a.leastHuCard;
            chanceToHu=a.chanceToHu;
            for(int i=0;i<4;++i) lastCard[i]=a.lastCard[i];
        }
    }
    void getShouPai(){
        for(int i=0;i<5;++i)for(int j=1;j<10;++j)shouPai[i][j]=c[i][j];
        for(int i=0;i<5;++i)for(int j=1;j<10;++j)
            shouPai[i][j]-=shun[i][j]+shun[i][j-1]+shun[i][j+1]+3*mingKe[i][j]+4*anGang[i][j]+4*mingGang[i][j];
    }
    void del(const char *s){
        int tp=getType(s);
        c[tp][s[1]-'0']--;totSize--;
    }
    void add(const char *s,int count=1){
        int tp=getType(s);
        if(tp==5)return ;
        c[tp][s[1]-'0']+=count;totSize+=count;
    }
    void add3(const char *s){
        int tp=getType(s);
        c[tp][s[1]-'0']++;totSize++;
        c[tp][s[1]-'0'+1]++;totSize++;
        c[tp][s[1]-'0'-1]++;totSize++;
    }
    void addShun(const char *s){
        int tp=getType(s);
        shun[tp][s[1]-'0']++;
        countOutCard++;
    }
    void addMingKe(const char *s){
        int tp=getType(s);
        mingKe[tp][s[1]-'0']++;
        countOutCard++;
    }
    void addMingGang(const char *s){
        int tp=getType(s);
        mingGang[tp][s[1]-'0']++;
        countOutCard++;
    }
    void addAnGang(const char *s){
        int tp=getType(s);
        anGang[tp][s[1]-'0']++;
        countOutCard++;
    }
    void changeLastCard(const char *s){
        for(int i=0;i<4;++i) lastCard[i]=s[i];
    }
}Card[4],outCard,tmpMyCard;
int diffCardlimit;
double useful[6][11];
int search_list[6][2];
int search_deep;
string qaz_err="";
vector<pair<string, pair<string, int> > > pack;
vector<string> hand;
string winTile;
void formatCard(){
    pack.clear();
    hand.clear();
    //tmpMyCard.getShouPai();
    for(int i=0;i<5;++i){
        for(int j=1;j<=9;++j){
            //添加明牌
            for(int tt=0;tt<tmpMyCard.shun[i][j];++tt) pack.push_back(mp("CHI",mp(intToString(i,j),2)));
            if(tmpMyCard.mingKe[i][j]) pack.push_back(mp("PENG",mp(intToString(i,j),2)));
            if(tmpMyCard.mingGang[i][j]) pack.push_back(mp("GANG",mp(intToString(i,j),2)));
            if(tmpMyCard.anGang[i][j]) pack.push_back(mp("GANG",mp(intToString(i,j),0)));
            //添加暗牌（手牌和暗杠？）
            /*
            if(tmpMyCard.anGang[i][j])
                for(int k=0;k<4;++k) hand.push_back(intToString(i,j));*/
            for(int k=0;k<tmpMyCard.shouPai[i][j];++k) hand.push_back(intToString(i,j));
        }
    }
}
void search();//下面写了
void searchUpdate();
void rebuildHuFa();
string judgeError;
int remCard[5][11];
db getassessHu(int p){
    db ans=255*255*255;
    for(int i=0;i<5;++i) for(int j=1;j<=9;++j) tmp[i][j]=tmpMyCard.shouPai[i][j];
    int tx,ty,tt;
    CARD ret;ret.copy(tmpMyCard);
    for(int i=0;i<4;++i){
        if(plan[p].outShun[i]){
            tx=plan[p].outShun[i]/10;ty=plan[p].outShun[i]%10;
            if(!tmpMyCard.shun[tx][ty]){
                tt=0;
                for(int j=-1;j<=1;++j){
                    if(tmp[tx][ty+j]) --tmp[tx][ty+j];
                    else ++tt,ans*=remCard[tx][ty+j]*1.0/255;
                }
                if(tt==3) ans*=18;
                else if(tt==2) ans*=6;
                else if(tt) ans*=2;
            }else tmpMyCard.shun[tx][ty]--;
        }
        if(plan[p].myShun[i]){
            tx=plan[p].myShun[i]/10;ty=plan[p].myShun[i]%10;
            for(int j=-1;j<=1;++j){
                if(tmp[tx][ty+j]) --tmp[tx][ty+j];
                else ans*=remCard[tx][ty+j]*3.0/255;
            }
        }
        if(plan[p].outKe[i]){
            tx=plan[p].outKe[i]/10;ty=plan[p].outKe[i]%10;
            if(!tmpMyCard.mingKe[tx][ty]){
                tt=0;
                for(int j=-1;j<=1;++j){
                    if(tmp[tx][ty]) --tmp[tx][ty];
                    else ans*=max(remCard[tx][ty]-tt,0)*1.0/255,++tt;
                }
                if(tt==3) ans*=50;
                else if(tt==2) ans*=30;
                else if(tt) ans*=15;
            }
        }
        if(plan[p].myKe[i]){
            tx=plan[p].myKe[i]/10;ty=plan[p].myKe[i]%10;
            tt=0;
            for(int j=-1;j<=1;++j){
                if(tmp[tx][ty]) --tmp[tx][ty];
                else ans*=max(remCard[tx][ty]-tt,0)*4.0/255,++tt;
            }
        }
        if(plan[p].outGang[i]){
            tx=plan[p].outGang[i]/10;ty=plan[p].outGang[i]%10;
            if(!tmpMyCard.mingGang[tx][ty]){
                tt=0;
                for(int j=-1;j<=2;++j){
                    if(tmp[tx][ty]) --tmp[tx][ty];
                    else ans*=max(remCard[tx][ty]-tt,0)*1.0/255,++tt;
                }
                if(tt==3) ans*=20;
                else if(tt==2) ans*=10;
                else if(tt) ans*=5;
            }
        }
        if(plan[p].anGang[i]){
            tx=plan[p].anGang[i]/10;ty=plan[p].anGang[i]%10;
            tt=0;
            for(int j=-1;j<=2;++j){
                if(tmp[tx][ty]) --tmp[tx][ty];
                else ans*=max(remCard[tx][ty]-tt,0)*3.0/255,++tt;
            }
        }
    }
    for(int i=0;i<7;++i){
        if(!plan[p].myduizi[i]) break;
        tx=plan[p].myduizi[i]/10;ty=plan[p].myduizi[i]%10;
        tt=0;
        for(int j=2;j;--j){
            if(tmp[tx][ty]) --tmp[tx][ty];
            else ans*=max(remCard[tx][ty]-tt,0)*3.0/255,++tt;
        }
    }
    tmpMyCard.copy(ret);
    if(ans>=255*255) ans*=3;
    return ans;
}
int mytmp[20],mytmp_cnt;
db dfs7dui(int dep,int z){
    if(!dep) return 255*255*255;
    db ta=0;
    for(int i=z,x,y;i<mytmp_cnt;++i){
        x=mytmp[i]/10;y=mytmp[i]%10;
        ta+=dfs7dui(dep-1,z+1)*remCard[x][y]*0.7/255;
    }
    return ta;
}
db assessHu(){
    db ans=0;
    memset(remCard,0,sizeof(remCard));
    for(int i=0;i<5;++i) for(int j=1;j<=9;++j)
        remCard[i][j]=4-outCard.c[i][j]-tmpMyCard.shouPai[i][j];
    for(int p=1;p<=huCnt;++p) ans+=getassessHu(p);
    //七小对
    memset(mytmp,0,sizeof(mytmp));mytmp_cnt=0;
    int pair_cnt=0,tot_cnt=0;
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        tot_cnt+=tmpMyCard.shouPai[i][j];
        pair_cnt+=tmpMyCard.shouPai[i][j]/2;
    }
    if(tot_cnt<13||pair_cnt<2||(7-pair_cnt)>Card[myID].leastHuCard) return ans;
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        if(tmpMyCard.shouPai[i][j]&1) mytmp[mytmp_cnt++]=i*10+j;
    }
    ans+=dfs7dui(7-pair_cnt,0);
    return ans;
}

void updateUseful(){
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        if(!tmpMyCard.shouPai[i][j]) continue;
        --tmpMyCard.shouPai[i][j];
        ++outCard.c[i][j];
        useful[i][j]=-assessHu();
        --outCard.c[i][j];
        if(Card[myID].leastHuCard>2){
            if((i>2&&tmpMyCard.shouPai[i][j]<1)||(i<=2&&(tmpMyCard.shouPai[i][j]<1)&&(!tmpMyCard.shouPai[i][j-1]&&!tmpMyCard.shouPai[i][j+1])&&((j>2&&!tmpMyCard.shouPai[i][j-2])||j<=2)&&(j>=8||(j<8&&!tmpMyCard.shouPai[i][j+2])))) useful[i][j]*=2;
            if((i<=2&&tmpMyCard.shouPai[i][j-1]&&tmpMyCard.shouPai[i][j+1])||tmpMyCard.shouPai[i][j]>1) useful[i][j]/=2;
        }
        ++tmpMyCard.shouPai[i][j];
    }
}
bool isuseless(int x,int y){
    updateUseful();
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        if(!tmpMyCard.shouPai[i][j]) continue;
        if(useful[i][j]<useful[x][y]) return false;
    }
    return true;
}
bool isJueZhang(const char *tmpCard){
    int tp=getType(tmpCard);
    return isMyTurn?(outCard.c[tp][tmpCard[1]-'0']==3):outCard.c[tp][tmpCard[1]-'0']==4;
}

int specialplay;
int sptmp[6][11];
bool judgeSpecial(char *tmpCard){
    if(tmpMyCard.countOutCard>0){
        specialplay=0;
        return 0;
    }
    memset(remCard,0,sizeof(remCard));
    for(int i=0;i<5;++i) for(int j=1;j<=9;++j)
        remCard[i][j]=4-outCard.c[i][j]-tmpMyCard.shouPai[i][j];
    // //七对
    // memset(tmp,0,sizeof(tmp));
    // int pair_cnt=0,tot_cnt=0;
    // for(int i=0;i<5;++i)for(int j=1;j<10;++j){
    //     tot_cnt+=tmpMyCard.shouPai[i][j];
    //     pair_cnt+=tmpMyCard.shouPai[i][j]/2;
    //     tmp[i][j]+=((tmpMyCard.shouPai[i][j]+1)/2)*2;
    //     if(outCard.c[i][j]+tmpMyCard.shouPai[i][j]>=4&&(tmpMyCard.shouPai[i][j]&1)) tmp[i][j]=5;
    // }
    //十三幺
    memset(sptmp,0,sizeof(sptmp));
    memset(useful,0,sizeof(useful));
    int dist=0,pair_cnt=0;
    for(int i=0;i<3;++i){
        sptmp[i][1]=sptmp[i][9]=sptmp[4][i+1]=2;
        if(!tmpMyCard.shouPai[i][1]){
            dist++;
            if(!remCard[i][1]) dist=100;
        }else useful[i][1]=10;
        if(!tmpMyCard.shouPai[i][9]){
            dist++;
            if(!remCard[i][9]) dist=100;
        }else useful[i][9]=10;
        if(!tmpMyCard.shouPai[4][i+1]){
            dist++;
            if(!remCard[4][i+1]) dist=100;
        }else useful[4][i+1]=10;
        if(tmpMyCard.shouPai[i][1]==2) pair_cnt=1,useful[i][1]=4+remCard[i][1];
        if(tmpMyCard.shouPai[i][9]==2) pair_cnt=1,useful[i][9]=4+remCard[i][9];
        if(tmpMyCard.shouPai[4][i+1]==2) pair_cnt=1,useful[4][i+1]=4+remCard[4][i+1];
    }
    for(int i=1;i<=4;++i){
        sptmp[3][i]=2;
        if(!tmpMyCard.shouPai[3][i]){
            dist++;
            if(!remCard[3][i]) dist=100;
        }else useful[3][i]=10;
        if(tmpMyCard.shouPai[3][i]==2) pair_cnt=1,useful[3][i]=4+remCard[3][i];
    }
    if(!pair_cnt) dist++;

    int arr[3]={0,1,2},tdis,tarr[3]={0,1,2};//下面用的 goto不让写下面qwq

    if(dist<4) goto play;

    //全不靠
    dist=14;
    memset(useful,0,sizeof(useful));
    for(int i=1;i<=4;++i){//东南西北
        if(tmpMyCard.shouPai[3][i]){
            dist--;
            if(tmpMyCard.shouPai[3][i]==1) useful[3][i]=10;
        }
    }
    for(int i=1;i<=3;++i){//中发白
        if(tmpMyCard.shouPai[4][i]){
            dist--;
            if(tmpMyCard.shouPai[4][i]==1) useful[4][i]=10;
        }
    }
    tdis=dist;//goto 不让在这定义变量w
    while(next_permutation(arr,arr+3)){//枚举组合方式
        int ttdis=dist;
        for(int i=0;i<3;++i){
            for(int j=1;j<8;j+=3){
                if(tmpMyCard.shouPai[arr[i]][j+i]){
                    ttdis--;
                }
            }
        }
        if(ttdis<tdis){//记录最优组合方式
            tdis=ttdis;
            for(int i=0;i<3;++i) tarr[i]=arr[i];
        }
    }
    dist=tdis;
    for(int i=0;i<3;++i) arr[i]=tarr[i];
    for(int i=0;i<3;++i){
        for(int j=1;j<8;j+=3){
            if(tmpMyCard.shouPai[arr[i]][j+i]==1)
                useful[arr[i]][j+i]=10;
        }
    }
    if(dist<4) goto play;

    specialplay=0;
    memset(useful,0,sizeof(useful));
    return 0;

play:
    int ii=0,jj=0;
    for(int i=4;i>=0;--i)for(int j=1;j<10;++j){
        if(tmpMyCard.shouPai[i][j]>0&&ii==0&&jj==0){
            ii=i,jj=j;
        }
        else if(tmpMyCard.shouPai[i][j]>0&&useful[ii][jj]>useful[i][j]) ii=i,jj=j;
    }
    if(!ii&&!jj){//万一出bug了，抓啥打啥？qaq
        response.push_back("PLAY "+string(tmpCard));
    }
    else response.push_back("PLAY "+intToString(ii,jj));
    memset(useful,0,sizeof(useful));
    specialplay=1;
    return 1;
}

bool haiDi(){
    for(int i=0;i<4;++i) if(!card_cnt[i]) return true;
    return false;
}
int judgeChi(const char *tmpCard){
    if(haiDi()) return false;
    if(specialplay) return false;
    int i=getType(tmpCard),j=tmpCard[1]-'0';
    if(i>2){
        return 0;
    }
    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();

    CARD ret;ret.copy(tmpMyCard);
    db ta=assessHu()/2,tb=0,ttb;
    int f=0;
    if(j>=3&&tmpMyCard.shouPai[i][j-2]>0&&tmpMyCard.shouPai[i][j-1]>0){
        char tttmp[4];strcpy(tttmp,intToString(i,j-1).c_str());
        tmpMyCard.addShun(tttmp);
        tmpMyCard.shouPai[i][j-2]--;tmpMyCard.shouPai[i][j-1]--;
        ++outCard.c[i][j-2];++outCard.c[i][j-1];
        ttb=assessHu();
        --outCard.c[i][j-2];--outCard.c[i][j-1];
        if(ttb>ta&&ttb>tb){
            f=1;
            tb=ttb;
        }
        tmpMyCard.copy(ret);
    }
    if(j>1&&j<9&&tmpMyCard.shouPai[i][j-1]>0&&tmpMyCard.shouPai[i][j+1]>0){
        char tttmp[4];strcpy(tttmp,intToString(i,j).c_str());
        tmpMyCard.addShun(tttmp);
        tmpMyCard.shouPai[i][j+1]--;tmpMyCard.shouPai[i][j-1]--;
        ++outCard.c[i][j+1];++outCard.c[i][j-1];
        ttb=assessHu();
        --outCard.c[i][j+1];--outCard.c[i][j-1];
        if(ttb>ta&&ttb>tb){
            f=2;
            tb=ttb;
        }
        tmpMyCard.copy(ret);
    }
    if(j<=7&&tmpMyCard.shouPai[i][j+2]>0&&tmpMyCard.shouPai[i][j+1]>0){
        char tttmp[4];strcpy(tttmp,intToString(i,j+1).c_str());
        tmpMyCard.addShun(tttmp);
        tmpMyCard.shouPai[i][j+2]--;tmpMyCard.shouPai[i][j+1]--;
        ++outCard.c[i][j+2];++outCard.c[i][j+1];
        ttb=assessHu();
        --outCard.c[i][j+2];--outCard.c[i][j+1];
        if(ttb>ta&&ttb>tb){
            f=3;
            tb=ttb;
        }
        tmpMyCard.copy(ret);
    }

    return f;
}
int judgePeng(const char *tmpCard){
    if(haiDi()) return false;
    if(specialplay) return false;
    int i=getType(tmpCard),j=tmpCard[1]-'0';
    if(Card[myID].shouPai[i][j]<2){
        return 0;
    }
    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();

    CARD ret;ret.copy(tmpMyCard);
    db ta=assessHu();
    int f=0;
    char tttmp[4];strcpy(tttmp,intToString(i,j).c_str());
    tmpMyCard.addMingKe(tttmp);
    tmpMyCard.shouPai[i][j]-=2;
    outCard.c[i][j]+=2;
    if(assessHu()*2>ta){
        f=1;
    }
    outCard.c[i][j]-=2;
    tmpMyCard.copy(ret);
    return f;
}
bool check7Dui(int lim){
    int pair_cnt=0,tot_cnt=0;
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        tot_cnt+=tmpMyCard.shouPai[i][j];
        pair_cnt+=tmpMyCard.shouPai[i][j]/2;
    }
    return tot_cnt>=13&&(7-pair_cnt)<=lim;
}
bool judgeGang(){//直接从自己手牌判断杠，其他不管了，标准useful<=1，有暗杠就杠 qaq
    if(!rebuild) return false;
    if(haiDi()) return false;
    // for(int i=0;i<5;++i)for(int j=1;j<10;++j){
    //     // if(tmpMyCard.shouPai[i][j]==4){
    //     //     //是否是七对
    //     //     if(check7Dui(3)) continue;
    //     //     //qwq
    //     //     char tttmp[4];strcpy(tttmp,intToString(i,j).c_str());
    //     //     Card[myID].anGang[i][j]++;Card[myID].countOutCard++;
    //     //     response.push_back("GANG "+intToString(i,j));
    //     //     return true;
    //     // }
    //     if(tmpMyCard.shouPai[i][j]>0&&Card[myID].mingKe[i][j]&&isuseless(i,j)){
    //         char tttmp[4];strcpy(tttmp,intToString(i,j).c_str());
    //         response.push_back("BUGANG "+intToString(i,j));
    //         return true;
    //     }
    // }
    return false;
}
bool judgeHu(const char *tmpCard,bool isGang=0){
    //Card[myID].add(tmpCard);
    MahjongInit();
    formatCard();
    int fan=0;
    bool isOK=0;
    try{
        auto re = MahjongFanCalculator(pack,hand,tmpCard,0,isMyTurn,isJueZhang(tmpCard),isGang,0,myID,quan);
        for(auto i : re){
            //cout << i.first << " " << i.second << endl;
            fan+=i.first;
        }
        isOK=(fan>=8);
        if(!isOK) cannotHuTime++;
    }catch(const string &error){
        errorTime++;
        int tt=0,sb=0;
        for(int i=0;i<5;++i) for(int j=1;j<=9;++j){
            tt+=tmpMyCard.shouPai[i][j];
            if(tmpMyCard.shun[i][j]||tmpMyCard.mingKe[i][j]||tmpMyCard.mingGang[i][j]||tmpMyCard.anGang[i][j]) sb=1;
        }
        judgeError+=error+" "+to_string(tt);judgeError+=" ";if(sb)judgeError+="sb ";
        isOK=false;
        //cout << error << endl;
    }
    return isOK;
}

void responseOther(const char *tmpCard,bool isGang=0){
    if(outCard.lastplayer==myID){
        response.push_back("PASS");
        return ;
    }
    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();
    if(outCard.lastplayer==-1){
        if(judgeHu(tmpCard,isGang)){
            response.push_back("HU");
        }else response.push_back("PASS");
        return ;
    }
    if(judgeHu(tmpCard,isGang)){
        response.push_back("HU");
        return ;
    }
    if(isGang){
        response.push_back("PASS");
        return ;
    }
    int fchi=0,fpeng=0;
    if(outCard.lastplayer==(myID-1+4)%4){
        if(rebuild) fchi=judgeChi(tmpCard);
    }
    if(fchi){
        tmpMyCard.copy(Card[myID]);
        tmpMyCard.getShouPai();
        int x=getType(tmpCard),y=tmpCard[1]-'0';
        char tttmp[4];strcpy(tttmp,intToString(x,y+fchi-2).c_str());
        tmpMyCard.addShun(tttmp);
        tmpMyCard.shouPai[x][y+fchi-3]--;
        tmpMyCard.shouPai[x][y+fchi-2]--;
        tmpMyCard.shouPai[x][y+fchi-1]--;
        tmpMyCard.shouPai[x][y]++;
        
        updateUseful();
        int ii=0,jj=0;
        for(int i=5;i>=0;--i)for(int j=1;j<10;++j){
            if(tmpMyCard.shouPai[i][j]>0&&ii==0&&jj==0){
                ii=i,jj=j;
            }
            if(tmpMyCard.shouPai[i][j]>0&&useful[ii][jj]>useful[i][j]) ii=i,jj=j;
        }
        response.push_back("CHI "+intToString(x,y+fchi-2)+" "+intToString(ii,jj));

    }
    else {
        if(rebuild) fpeng=judgePeng(tmpCard);
        if(fpeng){
            tmpMyCard.copy(Card[myID]);
            tmpMyCard.getShouPai();
            int x=getType(tmpCard),y=tmpCard[1]-'0';
            char tttmp[4];strcpy(tttmp,intToString(x,y).c_str());
            tmpMyCard.addMingKe(tttmp);
            tmpMyCard.shouPai[x][y]-=2;
            
            updateUseful();
            int ii=0,jj=0;
            for(int i=5;i>=0;--i)for(int j=1;j<10;++j){
                if(tmpMyCard.shouPai[i][j]>0&&ii==0&&jj==0){
                    ii=i,jj=j;
                }
                if(tmpMyCard.shouPai[i][j]>0&&useful[ii][jj]>useful[i][j]) ii=i,jj=j;
            }
            response.push_back("PENG "+intToString(ii,jj));
        }
        else response.push_back("PASS");
    }
}
inline bool judgeHu14(){
    bool ttt;
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        if(tmpMyCard.shouPai[i][j]>tmp[i][j]){
            char tmpGet[4];
            tmpGet[0]=(i==0?'W':(i==1?'B':(i==2?'T':(i==3?'F':'J'))));
            tmpGet[1]='0'+j;tmpGet[2]=tmpGet[3]='\0';
            --tmpMyCard.shouPai[i][j];
            if(Card[myID].leastHuCard==1){
                bool tmt=isMyTurn;
                isMyTurn=0;
                ttt=judgeHu(tmpGet);
                isMyTurn=1;
                ttt|=judgeHu(tmpGet);
                isMyTurn=tmt;
            }else if(Card[myID].leastHuCard>=3){
                bool tmt=isMyTurn;
                if(!Card[myID].countOutCard){
                    isMyTurn=0;
                }
                ttt=judgeHu(tmpGet);
                isMyTurn=tmt;
            }else ttt=judgeHu(tmpGet);
            ++tmpMyCard.shouPai[i][j];
            return ttt;
        }
    }
    return false;
}
bool canHu;
void search_best(int dist){
    for(int i=0;i<5;++i)for(int j=1;j<10;++j){
        if((i==3&&j>4)||(i==4&&j>3)) continue;
        if(i<search_list[search_deep+1][0]||(i==search_list[search_deep+1][0]&&j<=search_list[search_deep+1][1]))continue;
        if(turnID<4&&i>2&&tmpMyCard.shouPai[i][j]-tmp[i][j]<2)continue;
        if(outCard.c[i][j]+tmp[i][j]>2) continue;
        int dif=2-(tmpMyCard.shouPai[i][j]-tmp[i][j]);
        dif=min(max(dif,0),2);
        dist+=dif;
        if(dist>max(tmpMyCard.leastHuCard,3)){dist-=dif;continue;}
        search_list[++search_deep][0]=i,search_list[search_deep][1]=j;
        if(dif>0){for(int k=0;k<4;k++)if(!TMP.duizi[k]){TMP.duizi[k]=i*10+j;TMP.tt++;break;}}
        else {for(int k=0;k<4;k++)if(!TMP.myduizi[k]){TMP.myduizi[k]=i*10+j;TMP.tt++;break;}}
        tmp[i][j]+=2;
        //swap(tmpMyCard.shouPai,tmp);
        for(int x=0;x<5;++x) for(int y=1;y<=9;++y) swap(tmpMyCard.shouPai[x][y],tmp[x][y]);
        ++searchtime;
        if(judgeHu14()){
            //plan[++huCnt]=TMP;
            // if(tmpMyCard.leastHuCard>dist)huCnt=0;
            if(huCnt==4000){
            tmphucnt=(tmphucnt%4000)+1;
            plan[tmphucnt].init();
            plan[tmphucnt].copy(TMP);
            }
            else plan[++huCnt].copy(TMP);
            canHu=1;
            tmpMyCard.leastHuCard=min(tmpMyCard.leastHuCard,dist);
        }
        if(dif>0){for(int k=1;k>=0;k--)if(TMP.duizi[k]){TMP.duizi[k]=0;TMP.tt--;break;}}
        else {for(int k=1;k>=0;k--)if(TMP.myduizi[k]){TMP.myduizi[k]=0;TMP.tt--;break;}}
        dist-=dif;
        //swap(tmpMyCard.shouPai,tmp);
        for(int x=0;x<5;++x) for(int y=1;y<=9;++y) swap(tmpMyCard.shouPai[x][y],tmp[x][y]);
        tmp[i][j]-=2;
        if(searchtime>=searchtimelimit)return;
        search_list[search_deep][0]=search_list[search_deep][1]=0;
        search_deep--;
    }
}
void search_dfs_shun(int dep,int limit,int I,int J){
    if(!dep){
        search_best(diffCardlimit-limit);
        return ;
    }
    if(searchtime>=searchtimelimit) return;
    if(diffCardlimit-limit>max(tmpMyCard.leastHuCard,3))return ;
    for(int i=I;i<3;++i,J=2)for(int j=J;j<=8;++j){//枚举顺子
        if(i<search_list[search_deep+1][0]||(i==search_list[search_deep+1][0]&&j<search_list[search_deep+1][1]))continue;
        if(outCard.c[i][j]+tmp[i][j]>3) continue;
        if(outCard.c[i][j+1]+tmp[i][j+1]>3) continue;
        if(outCard.c[i][j-1]+tmp[i][j-1]>3) continue;
        int dif=0;
        if(tmpMyCard.shouPai[i][j]<=tmp[i][j])dif++;
        if(tmpMyCard.shouPai[i][j-1]<=tmp[i][j-1])dif++;
        if(tmpMyCard.shouPai[i][j+1]<=tmp[i][j+1])dif++;
        if(dif>limit)continue;
        search_list[++search_deep][0]=i,search_list[search_deep][1]=j;
        ++tmp[i][j];
        ++tmp[i][j-1];
        ++tmp[i][j+1];
        if(dif>0){for(int k=0;k<4;k++)if(!TMP.shun[k]){TMP.shun[k]=i*10+j;TMP.tt++;break;}}
        else {for(int k=0;k<4;k++)if(!TMP.myShun[k]){TMP.myShun[k]=i*10+j;TMP.tt++;break;}}
        search_dfs_shun(dep-1,limit-dif,i,j);
        if(dif>0){for(int k=3;k>=0;k--)if(TMP.shun[k]){TMP.shun[k]=0;TMP.tt--;break;}}
        else {for(int k=3;k>=0;k--)if(TMP.myShun[k]){TMP.myShun[k]=0;TMP.tt--;break;}}
        --tmp[i][j];
        --tmp[i][j-1];
        --tmp[i][j+1];
        if(searchtime>=searchtimelimit) return;
        search_list[search_deep][0]=search_list[search_deep][1]=0;
        search_deep--;
    }
}
void search_dfs_ke(int dep,int limit,int I,int J){
    if(!dep){
        search_best(diffCardlimit-limit);
        return ;
    }
    if(searchtime>=searchtimelimit) return;
    if(diffCardlimit-limit>max(tmpMyCard.leastHuCard,3))return ;

    for(int i=I;i<5;++i,J=1)for(int j=J;j<10;++j){//枚举刻子
        if(i<search_list[search_deep+1][0]||(i==search_list[search_deep+1][0]&&j<search_list[search_deep+1][1]))continue;
        if((i==3&&j>4)||(i==4&&j>3)) break;
        if(i>2&&tmpMyCard.shouPai[i][j]<2)continue;
        if(outCard.c[i][j]+tmp[i][j]>1) continue;
        //cerr<<i<<' '<<j<<endl;
        int dif=0;
        if(tmpMyCard.shouPai[i][j]<tmp[i][j])dif+=3;
        else if(tmpMyCard.shouPai[i][j]-tmp[i][j]<3)dif+=3-(tmpMyCard.shouPai[i][j]-tmp[i][j]);
        if(dif>limit) continue;
        search_list[++search_deep][0]=i,search_list[search_deep][1]=j;
        tmp[i][j]+=3;
        if(dif>0){for(int k=0;k<4;k++)if(!TMP.ke[k]){TMP.ke[k]=i*10+j;TMP.tt++;break;}}
        else {for(int k=0;k<4;k++)if(!TMP.myKe[k]){TMP.myKe[k]=i*10+j;TMP.tt++;break;}}
        search_dfs_ke(dep-1,limit-dif,i,j);
        if(dif>0){for(int k=3;k>=0;k--)if(TMP.ke[k]){TMP.ke[k]=0;TMP.tt--;break;}}
        else {for(int k=3;k>=0;k--)if(TMP.myKe[k]){TMP.myKe[k]=0;TMP.tt--;break;}}
        tmp[i][j]-=3;
        if(searchtime>=searchtimelimit){return;}
        search_list[search_deep][0]=search_list[search_deep][1]=0;
        search_deep--;
    }
    search_list[++search_deep][0]=10,search_list[search_deep][1]=10;
    search_dfs_shun(dep,limit,0,2);
    if(searchtime>=searchtimelimit) return;
    search_list[search_deep][0]=search_list[search_deep][1]=0;
    search_deep--;
}
void search(){
    TMP.init();
    for(int i=0;i<5;i++)for(int j=1;j<=9;j++){
        for(int zz=0;zz<tmpMyCard.shun[i][j];++zz){
            for(int k=0;k<4;k++)if(!TMP.outShun[k]){TMP.outShun[k]=i*10+j;break;}
        }
        if(tmpMyCard.mingKe[i][j]){
            for(int k=0;k<4;k++)if(!TMP.outKe[k]){TMP.outKe[k]=i*10+j;break;}
        }
        if(tmpMyCard.mingGang[i][j]){
            for(int k=0;k<4;k++)if(!TMP.outGang[k]){TMP.outGang[k]=i*10+j;break;}
        }
        if(tmpMyCard.anGang[i][j]){
            for(int k=0;k<4;k++)if(!TMP.anGang[k]){TMP.anGang[k]=i*10+j;break;}
        }
    }
    if(turnID==1){
        tmpMyCard.leastHuCard=6;//不然的话继承上次的
        if(tmpMyCard.leastHuCard<4) tmpMyCard.leastHuCard++;
        //judgeSpecial();//判断七小对十三幺等牌型
    }
    diffCardlimit=6;//最多允许有6张牌不一样
    memset(tmp,0,sizeof(tmp));
    search_deep=0;
    search_dfs_ke(4-tmpMyCard.countOutCard,diffCardlimit,0,1);
    if(searchtime<searchtimelimit){
        searchover=1;
    }
    Card[myID].leastHuCard=tmpMyCard.leastHuCard;
}

void buHua(int playerID,char *tmpCard){
    ++hua[playerID];
    Card[playerID].add(tmpCard);
    outCard.lastCard[0]='@';
    response.push_back("PASS");
}
void buGang(int playerID,char *tmpCard){
    int tp=getType(tmpCard);
    int tmp=tmpCard[1]-'0';
    Card[playerID].mingKe[tp][tmp]--;
    Card[playerID].mingGang[tp][tmp]++;
    outCard.add(tmpCard);
    outCard.lastplayer=-1;
    outCard.changeLastCard(tmpCard);
    if(playerID==myID)response.push_back("PASS");
    else responseOther(tmpCard,1);
}
void play(int playerID,char *tmpCard){
    Card[playerID].del(tmpCard);
    outCard.add(tmpCard);
    outCard.changeLastCard(tmpCard);
    responseOther(tmpCard);
}
int tpu[6][11];
bool iseasy = 0, researched = 0;
void easyplay(char *tmpCard){
    iseasy = 1;
    for(int i=0;i<5;++i)for(int j=1;j<=9;++j){
        if((i==3&&j>4)||(i==4&&j>3)) break;
        if(tmpMyCard.shouPai[i][j]>1) tpu[i][j]+=2;
        else if(tmpMyCard.shouPai[i][j]&&tmpMyCard.shouPai[i][j+1]&&i<3) tpu[i][j]+=1;
    }
    int ii=0,jj=0;
    for(int i=4;i>=0;--i)for(int j=1;j<10;++j){
        if(tmpMyCard.shouPai[i][j]>0&&ii==0&&jj==0){
            ii=i,jj=j;
        }
        else if(tmpMyCard.shouPai[i][j]>0&&tpu[ii][jj]>tpu[i][j]) ii=i,jj=j;
    }
    if(!ii&&!jj){//万一出bug了，抓啥打啥？qaq
        response.push_back("PLAY "+string(tmpCard));
    }
    else response.push_back("PLAY "+intToString(ii,jj));
}
void play(char *tmpCard){
    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();
    if(judgeHu(tmpCard)){
        response.push_back("HU");
        return;
    }
    Card[myID].add(tmpCard);
    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();

    if(judgeSpecial(tmpCard)){
        // specialPlay();
        //直接写了
        return;
    }

    if(!rebuild){
        easyplay(tmpCard);
        return;
    }
    searchUpdate();

    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();
    //从手牌判断杠
    if(judgeGang()){
        for(int i=1;i<=4000;i++)plan[i].init();
        huCnt=tmphucnt=0;
        tmpMyCard.copy(Card[myID]);
        if(response[turnID][0]=='B'){
            int tp=getType(tmpCard);
            int tmp=tmpCard[1]-'0';
            tmpMyCard.mingKe[tp][tmp]--;
            tmpMyCard.mingGang[tp][tmp]++;
        }
        tmpMyCard.getShouPai();
        
        searchover=0;rebuild=0;
        researched = 1;
        search();
        //直接在judgeGang里写response了
        return;
    }
    //判断打牌
    updateUseful();
    int ii=0,jj=0;
    for(int i=4;i>=0;--i)for(int j=1;j<10;++j){
        if(tmpMyCard.shouPai[i][j]>0&&ii==0&&jj==0){
            ii=i,jj=j;
        }
        else if(tmpMyCard.shouPai[i][j]>0&&useful[ii][jj]>useful[i][j]) ii=i,jj=j;
    }
    if(abs(useful[ii][jj])<0.00000001){
        easyplay(tmpCard);
        return;
    }
    if(!ii&&!jj){//万一出bug了，抓啥打啥？qaq
        response.push_back("PLAY "+string(tmpCard));
    }
    else response.push_back("PLAY "+intToString(ii,jj));
}

void peng(int playerID,char *tmpCard){
    outCard.add(outCard.lastCard,2);
    outCard.add(tmpCard);
    Card[playerID].addMingKe(outCard.lastCard);
    Card[playerID].add(outCard.lastCard);
    Card[playerID].del(tmpCard);
    outCard.changeLastCard(tmpCard);
    responseOther(tmpCard);
}
void chi(int playerID,char *tmpCard,char *tmpCard1){
    Card[playerID].add(outCard.lastCard);
    Card[playerID].addShun(tmpCard);
    Card[playerID].del(tmpCard1);
    outCard.del(outCard.lastCard);
    outCard.add3(tmpCard);
    outCard.add(tmpCard1);
    outCard.changeLastCard(tmpCard1);
    responseOther(tmpCard1);
}
void mingGang(int playerID){
    Card[playerID].add(outCard.lastCard);
    Card[playerID].addMingGang(outCard.lastCard);
    outCard.add(outCard.lastCard,3);
    outCard.lastCard[0]='@';
    response.push_back("PASS");
}
void work(){
    ostringstream sout;
    istringstream sin;
    //历史信息没什么卵用？先不读了（所有信息输出data就行吧
    sin.str(request[turnID]);
    int itmp,playerID;
    char tmpCard[4],tmpCard1[4],operation[10];
    sin>>itmp;
    switch (itmp){
    case 0:
        sin>>myID>>quan;
        response.push_back("PASS");
        break;
    case 1:
        for(int i=0;i<4;++i){
            sin>>hua[i];
            card_cnt[i]=21;
        }
        for(int i=0;i<13;++i){
            sin>>tmpCard;
            Card[myID].add(tmpCard);
        }
        tmpMyCard.copy(Card[myID]);
        tmpMyCard.getShouPai();
        researched = 1;
        search();
        //花牌好像也没什么用，具体信息没读qaq
        response.push_back("PASS");
        break;
    case 2:
        isMyTurn=1;
        sin>>tmpCard;
        --card_cnt[myID];
        outCard.lastCard[0]='@';
        //Card[myID].add(tmpCard);
        play(tmpCard);
        outCard.lastplayer=myID;
        break;
    case 3:
        sin>>playerID>>operation;
        outCard.lastplayer=playerID;
        switch(operation[0]){
            case 'B'://buhua or bugang
                sin>>tmpCard;
                if(operation[2]=='H'){//该消息会发送给所有玩家，表示玩家摸牌摸到花牌Card1，并补花。
                    buHua(playerID,tmpCard);
                }else{//该消息会发送给所有玩家，表示玩家进行了补杠操作，补杠Card1。
                    buGang(playerID,tmpCard);
                }
                break;
            case 'D'://表示其他玩家进行了摸牌操作。
                outCard.lastCard[0]='@';
                response.push_back("PASS");
                --card_cnt[playerID];
                break;
            case 'P'://play or peng
                if(operation[1]=='L'){ 
                    sin>>tmpCard;
                    play(playerID,tmpCard);
                    //该消息会发送给所有玩家，表示玩家摸牌后，直接打出了Card1。
                }else{ //该消息会发送给所有玩家，表示玩家进行了碰牌操作，碰的牌为上一回合打出的牌，并打出了Card1。
                    sin>>tmpCard;
                    peng(playerID,tmpCard);
                }
                break;
            case 'C'://该消息会发送给所有玩家，表示玩家进行了吃牌操作，吃牌后的顺子，中间牌为Card1，并打出Card2。
                sin>>tmpCard;
                sin>>tmpCard1;
                chi(playerID,tmpCard,tmpCard1);
                break;
            case 'G'://该消息会发送给所有玩家，表示玩家进行了杠牌操作，若上一回合为摸牌，表示进行暗杠，否则杠上回合打出的牌。
                if(outCard.lastCard[0]!='@') mingGang(playerID);
                else response.push_back("PASS");
                break;
        }
        break;
    default:
        break;
    }
    sin.clear();

}

string can_get_data="NO";
void getData(){
    string data;
    getline(cin, data);
    istringstream sin;
    sin.str(data);
    //code
    sin>>myID>>quan;
    for(int i=0;i<4;++i) sin>>hua[i];
    for(int i=0;i<4;++i) sin>>card_cnt[i];
    int len;
    sin>>len;
    for(int i=1;i<=len;i++)sin>>search_list[i][0]>>search_list[i][1];
    for(int p=0;p<4;++p){
        for(int i=0;i<6;++i)for(int j=1;j<10;++j)
            sin>>Card[p].c[i][j]>>Card[p].shun[i][j]>>Card[p].mingKe[i][j]\
               >>Card[p].anGang[i][j]>>Card[p].mingGang[i][j]>>Card[p].shouPai[i][j];
        sin>>Card[p].totSize;
        sin>>Card[p].countOutCard>>Card[p].lastplayer\
           >>Card[p].leastHuCard>>Card[p].chanceToHu;
        sin>>Card[p].lastCard;
    }
    for(int i=0;i<6;++i)for(int j=1;j<10;++j)
        sin>>outCard.c[i][j]>>outCard.shun[i][j]>>outCard.mingKe[i][j]\
           >>outCard.anGang[i][j]>>outCard.mingGang[i][j]>>outCard.shouPai[i][j];
    sin>>outCard.totSize;
    sin>>outCard.countOutCard>>outCard.lastplayer\
       >>outCard.leastHuCard>>outCard.chanceToHu;
    sin>>outCard.lastCard;

    sin>>searchover>>rebuild>>specialplay;
    sin>>huCnt>>tmphucnt;
    for(int p=1;p<=huCnt;++p){//shun ke dui ms mk md ag os ok og
        sin>>plan[p].tt;
        for(int i=1;i<=plan[p].tt;i++){
            sin>>plan[p].fuzi[i];
            switch(plan[p].fuzi[i]/100){
                case 0:for(int j=0;j<4;j++)if(plan[p].shun[j]==0){plan[p].shun[j]=plan[p].fuzi[i]%100;break;}break;
                case 1:for(int j=0;j<4;j++)if(plan[p].ke[j]==0){plan[p].ke[j]=plan[p].fuzi[i]%100;break;}break;
                case 2:for(int j=0;j<4;j++)if(plan[p].duizi[j]==0){plan[p].duizi[j]=plan[p].fuzi[i]%100;break;}break;
                case 3:for(int j=0;j<4;j++)if(plan[p].myShun[j]==0){plan[p].myShun[j]=plan[p].fuzi[i]%100;break;}break;
                case 4:for(int j=0;j<4;j++)if(plan[p].myKe[j]==0){plan[p].myKe[j]=plan[p].fuzi[i]%100;break;}break;
                case 5:for(int j=0;j<4;j++)if(plan[p].myduizi[j]==0){plan[p].myduizi[j]=plan[p].fuzi[i]%100;break;}break;
                case 6:for(int j=0;j<4;j++)if(plan[p].anGang[j]==0){plan[p].anGang[j]=plan[p].fuzi[i]%100;break;}break;
                case 7:for(int j=0;j<4;j++)if(plan[p].outShun[j]==0){plan[p].outShun[j]=plan[p].fuzi[i]%100;break;}break;
                case 8:for(int j=0;j<4;j++)if(plan[p].outKe[j]==0){plan[p].outKe[j]=plan[p].fuzi[i]%100;break;}break;
                case 9:for(int j=0;j<4;j++)if(plan[p].outGang[j]==0){plan[p].outGang[j]=plan[p].fuzi[i]%100;break;}break;
            }
        }
    }

    sin.clear();
    if(data.length()>10) can_get_data="YES";
}
template<class T>
inline void PUT(T x){
    cout<<x<<' ';
}
void PT(int x,int y,int p){
    if(x!=0)plan[p].fuzi[++plan[p].tt]=y*100+x;
}
void saveData(){
    PUT(myID);PUT(quan);
    for(int i=0;i<4;++i) PUT(hua[i]);
    for(int i=0;i<4;++i) PUT(card_cnt[i]);
    PUT(search_deep);
    for(int i=1;i<=search_deep;i++)PUT(search_list[i][0]),PUT(search_list[i][1]);
    for(int p=0;p<4;++p){
        for(int i=0;i<6;++i)for(int j=1;j<10;++j){
            PUT(Card[p].c[i][j]);PUT(Card[p].shun[i][j]);PUT(Card[p].mingKe[i][j]);
            PUT(Card[p].anGang[i][j]);PUT(Card[p].mingGang[i][j]);PUT(Card[p].shouPai[i][j]);
        }
        PUT(Card[p].totSize);
        PUT(Card[p].countOutCard);PUT(Card[p].lastplayer);
        PUT(Card[p].leastHuCard);PUT(Card[p].chanceToHu);
        PUT(Card[p].lastCard);
    }
    for(int i=0;i<6;++i)for(int j=1;j<10;++j){
        PUT(outCard.c[i][j]);PUT(outCard.shun[i][j]);PUT(outCard.mingKe[i][j]);
        PUT(outCard.anGang[i][j]);PUT(outCard.mingGang[i][j]);PUT(outCard.shouPai[i][j]);
    }
    PUT(outCard.totSize);
    PUT(outCard.countOutCard);PUT(outCard.lastplayer);
    PUT(outCard.leastHuCard);PUT(outCard.chanceToHu);
    PUT(outCard.lastCard);

    PUT(searchover);PUT(rebuild);PUT(specialplay);
    PUT(huCnt);
    PUT(tmphucnt);
    for(int p=1;p<=huCnt;++p){//shun ke dui ms mk md ag os ok og
        plan[p].tt=0;
        for(int i=0;i<4;++i){
            PT(plan[p].shun[i],0,p);PT(plan[p].ke[i],1,p);PT(plan[p].myShun[i],3,p);
            PT(plan[p].myKe[i],4,p);PT(plan[p].anGang[i],6,p);PT(plan[p].outShun[i],7,p);
            PT(plan[p].outKe[i],8,p);PT(plan[p].outGang[i],9,p);
        }
        for(int i=0;i<7;++i) PT(plan[p].myduizi[i],5,p),PT(plan[p].duizi[i],2,p);
        PUT(plan[p].tt);
        for(int i=1;i<=plan[p].tt;i++)PUT(plan[p].fuzi[i]);
    }
}
huFa tqaq[50010];
int tpHuCnt;
//距胡法差的张数
int getlhc(int p, int f=0){
    CARD ret;ret.copy(Card[myID]);
    ret.getShouPai();
    int tt=0,tans=0;
    for(int i=0,tx,ty;i<4;++i){
        tx=plan[p].shun[i]/10;ty=plan[p].shun[i]%10;
        if(ty) for(int j=-1;j<=1;++j) ret.shouPai[tx][ty+j]--;
        if(ty) ++tt;
        tx=plan[p].myShun[i]/10;ty=plan[p].myShun[i]%10;
        if(ty) for(int j=-1;j<=1;++j) ret.shouPai[tx][ty+j]--;
        if(ty) ++tt;
        tx=plan[p].ke[i]/10;ty=plan[p].ke[i]%10;
        if(ty) for(int j=-1;j<=1;++j) ret.shouPai[tx][ty]--;
        if(ty) ++tt;
        tx=plan[p].myKe[i]/10;ty=plan[p].myKe[i]%10;
        if(ty) for(int j=-1;j<=1;++j) ret.shouPai[tx][ty]--;
        if(ty) ++tt;
        tx=plan[p].outKe[i]/10;ty=plan[p].outKe[i]%10;
        if(ty) if(!ret.mingKe[tx][ty]){if(f){ret.shouPai[tx][ty]-=3;}else{tans+=100;}}
        if(ty) ++tt;
        tx=plan[p].outShun[i]/10;ty=plan[p].outShun[i]%10;
        if(ty) {if(ret.shun[tx][ty]<=0){if(f){for(int j=-1;j<=1;++j) ret.shouPai[tx][ty+j]--;}else{tans+=100;}};ret.shun[tx][ty]--;}
        if(ty) ++tt;
        tx=plan[p].outGang[i]/10;ty=plan[p].outGang[i]%10;
        if(ty) {if(!ret.mingGang[tx][ty])tans+=100;}
        if(ty) ++tt;
        tx=plan[p].anGang[i]/10;ty=plan[p].anGang[i]%10;
        if(ty) {if(!ret.anGang[tx][ty])tans+=100;}
        if(ty) ++tt;
    }
    if(tt<4) qaz_err+=to_string(tt)+" ";
    for(int i=0,tx,ty;i<7;++i){
        tx=plan[p].duizi[i]/10;ty=plan[p].duizi[i]%10;
        if(ty) ret.shouPai[tx][ty]-=2;
        tx=plan[p].myduizi[i]/10;ty=plan[p].myduizi[i]%10;
        if(ty) ret.shouPai[tx][ty]-=2;
    }
    for(int i=0;i<5;++i) for(int j=1;j<=9;++j){
        if(ret.shouPai[i][j]<0) tans-=ret.shouPai[i][j];
    }
    return tans;
}
int lhc=9999;//leasthucard
int LHC[100010];
void rebuildHuFa(int p){
    int tt=0;
    for(int i=0;i<4;++i){
        if(plan[p].shun[i]) ++tt;
        if(plan[p].ke[i]) ++tt;
    }
    for(int i=0;i<7;++i){
        if(plan[p].duizi[i]){
            for(int j=0;j<7;++j) if(!plan[p].myduizi[j]){
                plan[p].myduizi[j]=plan[p].duizi[i];
                plan[p].duizi[i]=0;
            }
        }
    }
    for(int z=0;z<(1<<tt);++z){
        huFa ret;ret.copy(plan[p]);
        for(int i=0,tz=0;i<4;++i){
            if(ret.shun[i]){
                if(z&(1<<tz)){
                    for(int j=0;j<4;++j) if(!ret.myShun[j]){
                        ret.myShun[j]=ret.shun[i];
                        ret.shun[i]=0;
                        break;
                    }
                }else{
                    for(int j=0;j<4;++j) if(!ret.outShun[j]){
                        ret.outShun[j]=ret.shun[i];
                        ret.shun[i]=0;
                        break;
                    }
                }
                ++tz;
            }
            if(ret.ke[i]){
                if(z&(1<<tz)){
                    for(int j=0;j<4;++j) if(!ret.myKe[j]){
                        ret.myKe[j]=ret.ke[i];
                        ret.ke[i]=0;
                        break;
                    }
                }else{
                    for(int j=0;j<4;++j) if(!ret.outKe[j]){
                        ret.outKe[j]=ret.ke[i];
                        ret.ke[i]=0;
                        break;
                    }
                }
                ++tz;
            }
        }
        
        CARD ttp;
        for(int i=0,tx,ty;i<4;++i){
            tx=ret.myShun[i]/10;ty=ret.myShun[i]%10;
            if(ty) for(int j=-1;j<=1;++j) ttp.c[tx][ty+j]++;
            tx=ret.outShun[i]/10;ty=ret.outShun[i]%10;
            if(ty){
                for(int j=-1;j<=1;++j) ttp.c[tx][ty+j]++;
                ttp.shun[tx][ty]++;
            }

            tx=ret.myKe[i]/10;ty=ret.myKe[i]%10;
            if(ty) for(int j=-1;j<=1;++j) ttp.c[tx][ty]++;
            tx=ret.outKe[i]/10;ty=ret.outKe[i]%10;
            if(ty){
                for(int j=-1;j<=1;++j) ttp.c[tx][ty]++;
                ttp.mingKe[tx][ty]++;
            }
            tx=ret.outGang[i]/10;ty=ret.outGang[i]%10;
            if(ty){
                for(int j=-1;j<=2;++j) ttp.c[tx][ty]++;
                ttp.mingGang[tx][ty]++;
            }
            tx=ret.anGang[i]/10;ty=ret.anGang[i]%10;
            if(ty){
                for(int j=-1;j<=2;++j) ttp.c[tx][ty]++;
                ttp.anGang[tx][ty]++;
            }
        }
        for(int i=0,tx,ty;i<7;++i){
            tx=ret.myduizi[i]/10;ty=ret.myduizi[i]%10;
            if(ty) ttp.c[tx][ty]+=2;
        }
        tmpMyCard.copy(ttp);
        tmpMyCard.getShouPai();
        Card[myID].getShouPai();

        if(lhc==1){
            int ii=0,jj=0;
            for(int i=0;i<5;++i) for(int j=1;j<=9;++j){
                if(tmpMyCard.shouPai[i][j]>Card[myID].shouPai[i][j]) ii=i,jj=j;
            }
            if(!ii&&!jj) continue;
            tmpMyCard.shouPai[ii][jj]--;
            char tttmp[4];strcpy(tttmp,intToString(ii,jj).c_str());
            bool ttt,tmt=isMyTurn;
            isMyTurn=0;
            ttt=judgeHu(tttmp);
            isMyTurn=1;
            ttt|=judgeHu(tttmp);
            isMyTurn=tmt;
            if(ttt) tqaq[++tpHuCnt]=ret;
            tmpMyCard.shouPai[ii][jj]++;
        }else{
            int ii=0,jj=0;
            for(int i=0;i<5;++i) for(int j=1;j<=9;++j){
                if(tmpMyCard.shouPai[i][j]&&!ii&&!jj) ii=i,jj=j;
                if(tmpMyCard.shouPai[i][j]>Card[myID].shouPai[i][j]){
                    ii=i,jj=j;
                    tmpMyCard.shouPai[ii][jj]--;
                    char tttmp[4];strcpy(tttmp,intToString(ii,jj).c_str());
                    if(judgeHu(tttmp)){
                        tqaq[++tpHuCnt]=ret;
                        tmpMyCard.shouPai[ii][jj]++;
                        break;
                    } 
                    tmpMyCard.shouPai[ii][jj]++;
                } 
            }
            // tmpMyCard.shouPai[ii][jj]--;
            // char tttmp[4];strcpy(tttmp,intToString(ii,jj).c_str());
            // if(judgeHu(tttmp)) tqaq[++tpHuCnt]=ret;
        }
    }
}
void rebuildHuFa(){
    tpHuCnt=0;
    rebuild=1;
    lhc=9999;
    for(int p=1;p<=huCnt;++p){
        LHC[p]=getlhc(p);
        if(LHC[p]!=0) lhc=min(lhc,LHC[p]);
    }
    for(int p=1;p<=huCnt;++p){
        if(lhc<LHC[p]-1) continue;
        rebuildHuFa(p);
        if(tpHuCnt>4000) break;
    }
    huCnt=tpHuCnt;
    huCnt=min(huCnt,4000);
    for(int p=1;p<=huCnt;++p) plan[p]=tqaq[p];
}
int main()
{
    /*
    freopen("temp.in","r",stdin);
    freopen("temp.out","w",stdout);//*/
    string stmp;
#if SIMPLEIO
    cin >> turnID;
    turnID--;
    getline(cin, stmp);
    for(int i = 0; i < turnID; ++i) {
        getline(cin, stmp);
        request.push_back(stmp);
        getline(cin, stmp);
        response.push_back(stmp);
    }
    getline(cin, stmp);
    request.push_back(stmp);
#else
    Json::Value inputJSON;
    cin >> inputJSON;
    turnID = inputJSON["responses"].size();
    for(int i = 0; i < turnID; ++i) {
        request.push_back(inputJSON["requests"][i].asString());
        response.push_back(inputJSON["responses"][i].asString());
    }
    request.push_back(inputJSON["requests"][turnID].asString());
#endif
    if(turnID) getData();
    if(!searchover&&turnID>1){
        tmpMyCard.copy(Card[myID]);
        tmpMyCard.getShouPai();
        researched = 1;
        search();
    }
    if(searchover&&!rebuild) rebuildHuFa();
    else if(turnID>0&&turnID%5==0){
        int x=6;
        Card[myID].getShouPai();
        for(int i=1;i<=huCnt;i++)x=min(x,getlhc(i));
        for(int i=1;i<=4000;i++)plan[i].init();
        int cntdui=0;
        for(int i=0;i<5;i++)for(int j=1;j<=9;j++)cntdui+=Card[myID].shouPai[i][j]/2;
        if(Card[myID].countOutCard!=0)cntdui=0;
        huCnt=tmphucnt=0;
        Card[myID].leastHuCard=min(min(x+1,5),7-cntdui);
        tmpMyCard.copy(Card[myID]);
        tmpMyCard.getShouPai();
        searchover=0;rebuild=0;
        researched = 1;
        search();
        if(!searchover){qaz_err+="ERROR!!!!!";}
        else rebuildHuFa();
    }
    work();
    // if(searchover&!rebuild)rebuildHuFa();

#if SIMPLEIO
    cout << response[turnID] << endl;
    //log
    if(iseasy)cout << "easyplay" << " ";
    if(specialplay)cout << "specialplay" << " ";
    if(!researched)cout << "not searched" <<" ";
    cout<<huCnt<<" "<<Card[myID].leastHuCard<<" ";
    cout<<"HD:"<<card_cnt[0]<<','<<card_cnt[1]<<','<<card_cnt[2]<<','<<card_cnt[3]<<' ';
    if(searchover) PUT("over");
    if(rebuild) PUT("reb");
    cout<<qaz_err<<" "<<judgeError<<' '<<searchtime<<' ';
    Card[myID].getShouPai();
    for(int i=0;i<5;i++)for(int j=1;j<=9;j++){
        if(Card[myID].shouPai[i][j]>0)cout<<intToString(i,j)<<" "<<useful[i][j]<<" ";
    }
    int ccnt = 0;
    for(int i=1;i<=huCnt;i++){
        if(getlhc(i,rebuild)>Card[myID].leastHuCard){/*cout<<"wrong hufa!!!"<<" ";*/continue;}
        ccnt += 1;
        if(ccnt > 5)break;
        for(int j=0,tx,ty;j<4;j++){
        tx=plan[i].shun[j]/10;ty=plan[i].shun[j]%10;
        if(ty) cout<<"shun"<<tx<<ty<<" ";
        tx=plan[i].myShun[j]/10;ty=plan[i].myShun[j]%10;
        if(ty) cout<<"myshun"<<tx<<ty<<" ";
        tx=plan[i].ke[j]/10;ty=plan[i].ke[j]%10;
        if(ty) cout<<"ke"<<tx<<ty<<" ";
        tx=plan[i].myKe[j]/10;ty=plan[i].myKe[j]%10;
        if(ty) cout<<"myke"<<tx<<ty<<" ";
        tx=plan[i].outKe[j]/10;ty=plan[i].outKe[j]%10;
        if(ty) cout<<"outke"<<tx<<ty<<" ";
        tx=plan[i].outShun[j]/10;ty=plan[i].outShun[j]%10;
        if(ty) cout<<"outshun"<<tx<<ty<<" ";
        tx=plan[i].outGang[j]/10;ty=plan[i].outGang[j]%10;
        if(ty) cout<<"outgang"<<tx<<ty<<" ";
        tx=plan[i].anGang[j]/10;ty=plan[i].anGang[j]%10;
        if(ty) cout<<"angang"<<tx<<ty<<" ";
        tx=plan[i].myduizi[j]/10;ty=plan[i].myduizi[j]%10;
        if(ty) cout<<"myduizi"<<tx<<ty<<" ";
        tx=plan[i].duizi[j]/10;ty=plan[i].duizi[j]%10;
        if(ty) cout<<"duizi"<<tx<<ty<<" ";
        }
    }
    cout<<endl;
    //data
    saveData();
    //globaldata
    cout<<endl;
#else
    Json::Value outputJSON;
    outputJSON["response"] = response[turnID];
    cout << outputJSON << endl;
#endif
//cerr<<searchtime<<' '<<clock();
    return 0;
}
void searchUpdate(){
    if(!searchover||!rebuild) return;
    int x=6;
    Card[myID].getShouPai();
    for(int i=1;i<=huCnt;i++)x=min(x,getlhc(i,1)+1);
    int cntdui=0;
    for(int i=0;i<5;i++)for(int j=1;j<=9;j++)cntdui+=Card[myID].shouPai[i][j]/2;
    if(Card[myID].countOutCard) cntdui=0;

    if(min(x,7-cntdui)>4) return;
    Card[myID].leastHuCard=min(x,7-cntdui);
    for(int i=1;i<=4000;i++)plan[i].init();
    huCnt=tmphucnt=0;
    tmpMyCard.copy(Card[myID]);
    tmpMyCard.getShouPai();
    searchover=0;rebuild=0;
    researched = 1;
    search();
    if(!searchover){qaz_err+="ERROR!!!!!";}
    else rebuildHuFa();
}
