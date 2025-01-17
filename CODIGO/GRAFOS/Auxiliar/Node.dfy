class Node
{
  var v: string
  var adyacentes: set<Node> 
  constructor  (c: string) {
    v := c;
    adyacentes := {};  // Initialize as an empty sequence
  }
}