ProofTreeNodeView = require('views/proof_tree_node_view').ProofTreeNodeView

class exports.ProofTreeView extends Backbone.View

  id: 'proof-tree-view'
  tagName: 'ul'
  className: 'tree'

  initialize: =>
    @getRoot().get('childTerms').bind "change", @render

  getRoot: =>
    @model.get('treeRoot')

  render: =>
    view = new ProofTreeNodeView model: @getRoot()
    @$(@el).html view.render().el