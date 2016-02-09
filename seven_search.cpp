#include <cstdio>
#include <iostream>
#include <unordered_map>
#include <functional>
#include <vector>
#include <algorithm>
#include <queue>
#include <iterator>

struct state
{
  std::vector<int> vec;
  bool operator<(const state &y) const
  {
    return vec.size() > y.vec.size();
  }
  bool operator==(const state &y) const
  {
    if(vec.size() != y.vec.size()) return false;
    else
      {
	std::vector<int> v1 = vec, v2 = y.vec;
	std::sort(v1.begin(), v1.end());
	std::sort(v2.begin(), v2.end());
	for(unsigned int i = 0; i < vec.size(); i ++)
	  if(v1[i] != v2[i]) return false;
	return true;
      }
  }
};

struct state_hasher
{
  typedef state argument_type;
  typedef size_t result_type;
    
  result_type operator()(const state &x1) const throw()
  {
    state x = x1;
    sort(x.vec.begin(), x.vec.end());
    result_type m = 23237;

    for(auto t : x.vec)
      {
	m *= 39;
	m += t;
      }
      
    return m;
  }
};

struct state_trans
{
  int num;
  state prev;
};

// 0 -> forward, 1 -> backward
std::unordered_map<state, state_trans, state_hasher> vis[2];
std::priority_queue<state> more[2];

template<typename It>
void output_sol(int dir, const state &x, It it)
{
  for(auto nxt = vis[dir].find(x);
      nxt != vis[dir].end();
      nxt = vis[dir].find(nxt->second.prev))
    {
      *it = nxt->second.num;
    }
}

void pass(int dir)
{
  state x = more[dir].top();
  more[dir].pop();
  
  for(unsigned int i = 0; i < x.vec.size(); i ++)
    {
      if(x.vec[i] > 0)
	{
	  state news = state();
	  news.vec.push_back(x.vec[i] - 1);
	  news.vec.push_back(x.vec[i] + 1);

	  for(unsigned int j = 0; j < x.vec.size(); j ++)
	    if(i != j)
	      news.vec.push_back(x.vec[j]);

	  if(vis[! dir].count(news) >= 1)
	    {
	      std::cerr << "- Found.\n";
	      if(!dir) std::cout << "symmetry.\n";
	      
	      std::vector<int> S1;
	      output_sol(dir, x, back_inserter(S1));
	      
	      for(auto i = S1.rbegin(); i != S1.rend(); i ++)
		{
		  std::cout << "split_tree " << *i << ".\n";
		}
	      std::cout << "split_tree " << x.vec[i] << ".\n";
	      
	      std::cout << "symmetry.\n";

	      std::vector<int> S2;
	      output_sol(!dir, news, back_inserter(S2));
		  
	      for(auto i = S2.rbegin(); i != S2.rend(); i ++)
		{
		  std::cout << "split_tree " << *i << ".\n";
		}
	      std::cout << "ring.\n";

	      exit(0);
	    }
	  else if(vis[dir].count(news) == 0)
	    {
	      vis[dir].insert(std::make_pair(news, (state_trans){x.vec[i], x}));
	      more[dir].push(news);
	    }
	}
    }
}

int main()
{
  state s1 = state(), s7 = state();
  s1.vec.push_back(1);
  s7.vec.push_back(7);
  
  more[0].push(s1);
  
  more[1].push(s7);

  while(true)
    {
      pass(0);
      pass(1);
    }
}
