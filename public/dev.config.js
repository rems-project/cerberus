const Path = require('path');
const ExtractTextPlugin = require('extract-text-webpack-plugin')
//const BundleAnalyzerPlugin = require('webpack-bundle-analyzer').BundleAnalyzerPlugin;
// https://hackernoon.com/optimising-your-application-bundle-size-with-webpack-e85b00bab579

const extractCSS = new ExtractTextPlugin({ filename: 'style.bundle.css' })

module.exports = {
  mode: 'development',
  entry: './src/index.ts',
  output: {
    filename: '[name].bundle.js',
    path: Path.resolve(__dirname, 'dist')
  },
  externals: [
    'fs'
  ],
  resolve: {
    extensions: [".ts", ".js"]
  },
  /*
  optimization: {
    splitChunks: {
      cacheGroups: {
        vis: {
          test: /[\\/]node_modules\/vis[\\/]/,
          name: 'vis',
          chunks: 'all',
        },
        codemirror: {
          test: /[\\/]node_modules\/codemirror[\\/]/,
          name: 'codemirror',
          chunks: 'all',
        },
      },
    },
  },
  */
  module: {
    rules: [{
        test: /\.tsx?$/,
        use: 'ts-loader',
        exclude: [/node_modules/, /tests/]
      }, {
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
};

