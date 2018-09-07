const merge = require('webpack-merge');
const baseConfig = require('./base.config.js');
const ExtractTextPlugin = require('extract-text-webpack-plugin')
const extractCSS = new ExtractTextPlugin({ filename: 'style.bundle.css' })
//const BundleAnalyzerPlugin = require('webpack-bundle-analyzer').BundleAnalyzerPlugin;
// https://hackernoon.com/optimising-your-application-bundle-size-with-webpack-e85b00bab579

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
    extractCSS,
//    new BundleAnalyzerPlugin()
  ]
});

