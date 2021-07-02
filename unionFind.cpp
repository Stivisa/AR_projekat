#include "unionFind.hpp"
#include <set>

UnionFind::UnionFind(TermSet &t, UseMap &u) : _map(u)
{
   int i=0;
   for(auto term: t)
   {
      Node *n = new Node();
      n->t = term; 
      n->parent = n;
      n->rank = 0;
      n->position = i;
      _nodes.push_back(n);
      i++;
   }
}
int UnionFind::findPosition(Term s) const{
   for(unsigned i = 0; i < _nodes.size(); i++)
      if(s->equalTo(_nodes[i]->t)){
         return i;
      }
   return -1;
}

int UnionFind::findRootOfTerm(Term t) const{
   Node *current;
   unsigned i = findPosition(t);
   if(i==-1)
      return -1;
   current = _nodes[i];
   while(current->parent != current)
      current = current->parent;
   return current->position;
}

TermSet UnionFind::findAllRoots() const{
   TermSet roots;
   for(unsigned i = 0; i < _nodes.size(); i++){
      int j = findRootOfTerm(_nodes[i]->t);
      roots.insert(_nodes[j]->t);
   }
   return roots;
}
set<Node*> UnionFind::findAllRootNodes() const{
   set<Node*> nodes;
   for(unsigned i = 0; i < _nodes.size(); i++){
      int j = findRootOfTerm(_nodes[i]->t);
      nodes.insert(_nodes[j]);
   }
   return nodes;
}

void UnionFind::unionOfSets(Term firstTerm, Term secondTerm){
   Node* firstSet = _nodes[findRootOfTerm(firstTerm)];
   Node* secondSet = _nodes[findRootOfTerm(secondTerm)];

   if(firstSet == secondSet)
      return;

   if(firstSet->rank > secondSet->rank)
      secondSet->parent = firstSet;
   else if(firstSet->rank < secondSet->rank)
      firstSet->parent = secondSet;
   else{
      secondSet->parent = firstSet;
      firstSet->rank++; 
   }
}

TermSet UnionFind::findTermsFromTheSameSet(Term t) const{
   TermSet set;
   unsigned i = findPosition(t);
   int root1 = findRootOfTerm(t);
   for(unsigned j=0;j<_nodes.size();j++){
      int root2 = findRootOfTerm(_nodes[j]->t);
      if(j!=i && root1==root2)
         set.insert(_nodes[j]->t);
   }
   return set;
}

void UnionFind::printUnionFind() const{
   set<Node*> roots = findAllRootNodes();
   int i=0;
   for (auto root: roots){
      cout << "Klasa kongruencije " << i << ": " << root->t;
      TermSet equivalencySet = findTermsFromTheSameSet(root->t);
      for(auto term: equivalencySet){
         cout << " , " << term;
      }
      cout << endl;
      i++;
   }

}

UseMap& UnionFind::getUMap(){
   return _map;
}
UnionFind::~UnionFind(){
   for(unsigned i=0;i<_nodes.size();i++){
      delete _nodes[i];
   }
}
