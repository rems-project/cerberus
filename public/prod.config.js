const Path = require('path');
const CompressionPlugin = require("compression-webpack-plugin")
const ExtractTextPlugin = require('extract-text-webpack-plugin')
const extractCSS = new ExtractTextPlugin({ filename: 'style.bundle.css' })

module.exports = {
  entry: './src/index.ts',
  mode: 'production',
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
    },{
      test: /\.css$/,
      use: extractCSS.extract({
        fallback: 'style-loader',
        use: [ { loader: 'css-loader', options: { minimize: true } } ]
      })
    }
   ]
  },
  plugins: [
    extractCSS,
    new CompressionPlugin()
  ]
};

