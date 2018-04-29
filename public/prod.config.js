const merge = require('webpack-merge');
const baseConfig = require('./base.config.js');
const ExtractTextPlugin = require('extract-text-webpack-plugin')
const extractCSS = new ExtractTextPlugin({ filename: 'style.bundle.css' })

module.exports = merge(baseConfig, {
  mode: 'production',
  optimization: {
    splitChunks: {
      cacheGroups: {
        commons: {
          test: /[\\/]node_modules\/vis[\\/]/,
          name: 'vis',
          chunks: 'all',
        },
        commons2: {
          test: /[\\/]node_modules\/codemirror[\\/]/,
          name: 'codemirror',
          chunks: 'all',
        },
      },
    },
  },
  module: {
    rules: [{
      test: /\.css$/,
      use: extractCSS.extract({
        fallback: 'style-loader',
        use: [ { loader: 'css-loader', options: { minimize: true } } ]
      })
    }
   ]
  },
  plugins: [
    extractCSS
  ]
});

