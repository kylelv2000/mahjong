#include "MahjongGB/MahjongGB.h"
#include <iostream>
#include<ctime>
using namespace std;
int main() {
    
    int T=20000,ans;
    MahjongInit();
    try{
        auto re = MahjongFanCalculator({},{"W1","W1","W5","W6","W6","W7","W7","W8","T7","T8","T9","B1","B2"},"B3",1,0,0,0,0,0,0);
        for(auto i : re){
            ans+=i.first;
            cout << i.first << " " << i.second << endl;
        }
    }catch(const string &error){
        cout << error << endl;
    }
    while(T--){
    MahjongInit();
    try{
        auto re = MahjongFanCalculator({{"GANG",{"W1",1}}},{"W2","W2","W2","W3","W3","W3","W4","W4","W4","W5"},"W5",1,0,0,0,0,0,0);
        for(auto i : re){
            ans+=i.first;
            //cout << i.first << " " << i.second << endl;
        }
    }catch(const string &error){
        //cout << error << endl;
    }
    //cout << "----------" << endl;

    try{
        auto re = MahjongFanCalculator({{"GANG",{"W1",1}},{"CHI",{"T2",2}}},{"W3","W3","W3","W4","W4","W4","W5"},"W5",1,0,0,0,0,0,0);
        for(auto i : re){
            ans+=i.first;
            //cout << i.first << " " << i.second << endl;
        }
    }catch(const string &error){
        //cout << error << endl;
    }
    //cout << "----------" << endl;

    /*/No HU
    try{
        auto re = MahjongFanCalculator({{"GANG",{"W1",1}},{"CHI",{"T2",2}}},{"W3","W3","W3","W4","W4","W4","W5"},"W7",1,0,0,0,0,0,0);
        for(auto i : re){
            ans+=i.first;
            //cout << i.first << " " << i.second << endl;
        }
    }catch(const string &error){
        //cout << error << endl;
    }*/
    }
    cerr<<clock();
    return 0;
}
