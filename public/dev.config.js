const merge = require('webpack-merge');
const baseConfig = require('./base.config.js');
const ExtractTextPlugin = require('extract-text-webpack-plugin')
const extractCSS = new ExtractTextPlugin({ filename: 'style.bundle.css' })

module.exports = merge(baseConfig, {
  mode: 'development',
  module: {
    rules: [{
        test: /\.css$/,
        use: extractCSS.extract({
          fallback: 'style-loader',
          use: [ 'css-loader' ]
        })
      }
    ]
  },
  plugins: [
    extractCSS
  ]
});

