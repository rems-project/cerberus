const path = require('path');

module.exports = {
  entry: './src/index.ts',
  mode: 'production',
  output: {
    filename: '[name].bundle.js',
    path: path.resolve(__dirname, 'dist')
  },
  resolve: {
    extensions: [".ts", ".js"]
  },
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
  module: {
    rules: [{
        test: /\.tsx?$/,
        use: 'ts-loader',
        exclude: [/node_modules/, /tests/]
      }
    ]
  }
};

