const Path = require('path');
const ExtractTextPlugin = require('extract-text-webpack-plugin')
const extractCSS = new ExtractTextPlugin({ filename: 'style.bundle.css' })

module.exports = {
  mode: 'development',
  devtool: 'source-map',
  entry: './src/index.ts',
  output: {
    devtoolModuleFilenameTemplate: '[absolute-resource-path]',
    filename: '[name].bundle.js',
    path: Path.resolve(__dirname, 'dist')
  },
  node: {
    fs: "empty"
  },
  resolve: {
    extensions: [".ts", ".js"]
  },
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
  plugins: [ extractCSS ]
};

